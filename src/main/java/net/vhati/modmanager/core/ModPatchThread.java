package net.vhati.modmanager.core;

import java.io.BufferedInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.InputStream;
import java.io.IOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

import org.jdom2.JDOMException;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import net.vhati.ftldat.AbstractPack;
import net.vhati.ftldat.FTLPack;
import net.vhati.ftldat.PkgPack;
import net.vhati.ftldat.PackContainer;
import net.vhati.ftldat.PackUtilities;

import org.apache.commons.io.FileUtils;
import org.apache.commons.io.input.CloseShieldInputStream;


public class ModPatchThread extends Thread {

	private static final Logger log = LoggerFactory.getLogger( ModPatchThread.class );

	private static final String slipstreamIdentifierResource = "slipstream-identifier.xml";

	// Other threads can check or set this.
	public volatile boolean keepRunning = true;

	private Thread shutdownHook = null;

	private List<File> modFiles = new ArrayList<File>();
	private File datsDir = null;
	private File backupDir = null;
	private boolean globalPanic = false;
	private ModPatchObserver observer = null;

	private final int progMax = 100;
	private final int progBackupMax = 25;
	private final int progClobberMax = 25;
	private final int progModsMax = 40;
	private final int progRepackMax = 5;
	private int progMilestone = 0;


	public ModPatchThread( List<File> modFiles, File datsDir, File backupDir, boolean globalPanic, ModPatchObserver observer ) {
		this.modFiles.addAll( modFiles );
		this.datsDir = datsDir;
		this.backupDir = backupDir;
		this.globalPanic = globalPanic;
		this.observer = observer;
	}


	public void run() {
		boolean result;
		Exception exception = null;

		// When JVM tries to exit, stall until this thread ends on its own.
		shutdownHook = new Thread() {
			@Override
			public void run() {
				keepRunning = false;
				boolean interrupted = false;
				try {
					while ( ModPatchThread.this.isAlive() ) {
						try {
							ModPatchThread.this.join();
						}
						catch ( InterruptedException e ) {
							interrupted = true;
						}
					}
				}
				finally {
					if ( interrupted ) Thread.currentThread().interrupt();
				}
			}
		};
		Runtime.getRuntime().addShutdownHook( shutdownHook );

		try {
			result = patch();
		}
		catch ( Exception e ) {
			log.error( "Patching failed.", e );
			exception = e;
			result = false;
		}

		observer.patchingEnded( result, exception );

		Runtime.getRuntime().removeShutdownHook( shutdownHook );
	}


	private boolean patch() throws IOException, JDOMException {

		observer.patchingProgress( 0, progMax );

		PackContainer packContainer = null;

		try {
			int backupsCreated = 0;
			int datsClobbered = 0;
			int modsInstalled = 0;
			int datsRepacked = 0;

			File ftlDatFile = new File( datsDir, "ftl.dat" );
			File dataDatFile = new File( datsDir, "data.dat" );
			File resourceDatFile = new File( datsDir, "resource.dat" );

			List<BackedUpDat> backedUpDats = new ArrayList<BackedUpDat>( 2 );
			for ( File datFile : new File[] {ftlDatFile, dataDatFile, resourceDatFile} ) {
				if ( !datFile.exists() ) continue;

				BackedUpDat bud = new BackedUpDat();
				bud.datFile = datFile;
				bud.bakFile = new File( backupDir, datFile.getName() +".bak" );
				backedUpDats.add( bud );
			}

			// Don't let dats be read-only.
			for ( BackedUpDat bud : backedUpDats ) {
				if ( bud.datFile.exists() ) bud.datFile.setWritable( true );
			}

			// Create backup dats, if necessary.
			for ( BackedUpDat bud : backedUpDats ) {
				if ( !bud.bakFile.exists() ) {
					log.info( String.format( "Backing up \"%s\".", bud.datFile.getName() ) );
					observer.patchingStatus( String.format( "Backing up \"%s\".", bud.datFile.getName() ) );

					PackUtilities.copyFile( bud.datFile, bud.bakFile );
					backupsCreated++;
					observer.patchingProgress( progMilestone + progBackupMax/backedUpDats.size()*backupsCreated, progMax );

					if ( !keepRunning ) return false;
				}
			}
			progMilestone += progBackupMax;
			observer.patchingProgress( progMilestone, progMax );
			observer.patchingStatus( null );

			if ( backupsCreated != backedUpDats.size() ) {
				// Clobber current dat files with their respective backups.
				// But don't bother if we made those backups just now.

				for ( BackedUpDat bud : backedUpDats ) {
					log.info( String.format( "Restoring vanilla \"%s\"...", bud.datFile.getName() ) );
					observer.patchingStatus( String.format( "Restoring vanilla \"%s\"...", bud.datFile.getName() ) );

					PackUtilities.copyFile( bud.bakFile, bud.datFile );
					datsClobbered++;
					observer.patchingProgress( progMilestone + progClobberMax/backedUpDats.size()*datsClobbered, progMax );

					if ( !keepRunning ) return false;
				}
				observer.patchingStatus( null );
			}
			progMilestone += progClobberMax;
			observer.patchingProgress( progMilestone, progMax );

			if ( modFiles.isEmpty() ) {
				// No mods. Nothing else to do.
				observer.patchingProgress( progMax, progMax );
				return true;
			}

			String ultimateEncoding = null;

			packContainer = new PackContainer();
			if ( ftlDatFile.exists() ) {  // FTL 1.6.1.
				AbstractPack ftlPack = new PkgPack( ftlDatFile, "r+" );

				packContainer.setPackFor( "audio/", ftlPack );
				packContainer.setPackFor( "data/", ftlPack );
				packContainer.setPackFor( "fonts/", ftlPack );
				packContainer.setPackFor( "img/", ftlPack );
				packContainer.setPackFor( null, ftlPack );
				// Supposedly "exe_icon.png" has been observed at top-level?

				ultimateEncoding = "UTF-8";
			}
			else if ( dataDatFile.exists() && resourceDatFile.exists() ) {  // FTL 1.01-1.5.13.
				AbstractPack dataPack = new FTLPack( dataDatFile, "r+" );
				packContainer.setPackFor( "data/", dataPack );

				AbstractPack resourcePack = new FTLPack( resourceDatFile, "r+" );
				packContainer.setPackFor( "audio/", resourcePack );
				packContainer.setPackFor( "fonts/", resourcePack );
				packContainer.setPackFor( "img/", resourcePack );

				ultimateEncoding = "windows-1252";
			}
			else {
				throw new IOException( String.format( "Could not find either \"%s\" or both \"%s\" and \"%s\"", ftlDatFile.getName(), dataDatFile.getName(), resourceDatFile.getName() ) );
			}
			packContainer.setPackFor( "mod-appendix/", null );

			// Track modified innerPaths in case they're clobbered.
			List<String> moddedItems = new ArrayList<String>();

			List<String> knownPaths = new ArrayList<String>();
			for ( AbstractPack pack : packContainer.getPacks() ) {
				knownPaths.addAll( pack.list() );
			}

			List<String> knownPathsLower = new ArrayList<String>( knownPaths.size() );
			for ( String innerPath : knownPaths ) {
				knownPathsLower.add( innerPath.toLowerCase() );
			}

			List<String> knownRoots = packContainer.getRoots();

			// Group1: parentPath/, Group2: root/, Group3: fileName.
			Pattern pathPtn = Pattern.compile( "^(?:(([^/]+/)(?:.*/)?))?([^/]+)$" );

			// only occurs after checking at least one mod is selected
			String metadataFilename = "self-metadata.ftl";
			if ( !ftlDatFile.exists() ) metadataFilename = "self-metadata-legacy.ftl";
			InputStream metadataStream = getClass().getResourceAsStream( "/" + metadataFilename );

			File selfMetadataMod = null;
			if ( metadataStream == null ) {
				warnLogMetadataNotFound();
			}
			else {
				selfMetadataMod = File.createTempFile("SMM-", ".ftl");
				FileUtils.copyInputStreamToFile( metadataStream, selfMetadataMod );
				metadataStream.close();
				modFiles.add( 0, selfMetadataMod );
			}

			for ( File modFile : modFiles ) {
				if ( !keepRunning ) return false;

				FileInputStream fis = null;
				ZipInputStream zis = null;
				try {
					if ( modFile.equals( selfMetadataMod ) ) {
						log.info( "Installing mods..." );
						observer.patchingStatus( "Installing mods..." );
					}
					else {
						log.info( "" );
						log.info( String.format( "Installing mod: %s", modFile.getName() ) );
						observer.patchingMod( modFile );
					}
					fis = new FileInputStream( modFile );
					zis = new ZipInputStream( new BufferedInputStream( fis ) );
					ZipEntry item;
					while ( (item = zis.getNextEntry()) != null ) {
						if ( item.isDirectory() ) {
							zis.closeEntry();
							continue;
						}

						String innerPath = item.getName();
						innerPath = innerPath.replace( '\\', '/' );  // Non-standard zips.

						Matcher m = pathPtn.matcher( innerPath );
						if ( !m.matches() ) {
							log.warn( String.format( "Unexpected innerPath: %s", innerPath ) );
							zis.closeEntry();
							continue;
						}

						String parentPath = m.group( 1 );
						String root = m.group( 2 );
						String fileName = m.group( 3 );

						AbstractPack pack = packContainer.getPackFor( innerPath );
						if ( pack == null ) {
							if ( !knownRoots.contains( root ) ) {
								log.warn( String.format( "Unexpected innerPath: %s", innerPath ) );
							} else {
								log.debug( String.format( "Ignoring innerPath with known root: %s", innerPath ) );
							}
							zis.closeEntry();
							continue;
						}

						if ( ModUtilities.isJunkFile( innerPath ) ) {
							log.warn( String.format( "Skipping junk file: %s", innerPath ) );
							zis.closeEntry();
							continue;
						}

						if ( fileName.endsWith( ".xml.append" ) || fileName.endsWith( ".append.xml" ) ) {
							innerPath = parentPath + fileName.replaceAll( "[.](?:xml[.]append|append[.]xml)$", ".xml" );
							innerPath = checkCase( innerPath, knownPaths, knownPathsLower );

							if ( !pack.contains( innerPath ) ) {
								log.warn( String.format( "Non-existent innerPath wasn't appended: %s", innerPath ) );
							}
							else {
								InputStream mainStream = null;
								try {
									mainStream = pack.getInputStream( innerPath );
									InputStream mergedStream = ModUtilities.patchXMLFile( mainStream, zis, ultimateEncoding, globalPanic, pack.getName()+":"+innerPath, modFile.getName()+":"+parentPath+fileName );
									mainStream.close();
									pack.remove( innerPath );
									pack.add( innerPath, mergedStream );
								}
								finally {
									try {if ( mainStream != null ) mainStream.close();}
									catch ( IOException e ) {}
								}

								if ( !moddedItems.contains( innerPath ) ) {
									moddedItems.add( innerPath );
								}
							}
						}
						else if ( fileName.endsWith( ".xml.rawappend" ) || fileName.endsWith( ".rawappend.xml" ) ) {
							innerPath = parentPath + fileName.replaceAll( "[.](?:xml[.]rawappend|rawappend[.]xml)$", ".xml" );
							innerPath = checkCase( innerPath, knownPaths, knownPathsLower );

							if ( !pack.contains( innerPath ) ) {
								log.warn( String.format( "Non-existent innerPath wasn't raw appended: %s", innerPath ) );
							}
							else {
								log.warn( String.format( "Appending xml as raw text: %s", innerPath ) );
								InputStream mainStream = null;
								try {
									mainStream = pack.getInputStream( innerPath );
									InputStream mergedStream = ModUtilities.appendXMLFile( mainStream, zis, ultimateEncoding, pack.getName()+":"+innerPath, modFile.getName()+":"+parentPath+fileName );
									mainStream.close();
									pack.remove( innerPath );
									pack.add( innerPath, mergedStream );
								}
								finally {
									try {if ( mainStream != null ) mainStream.close();}
									catch ( IOException e ) {}
								}

								if ( !moddedItems.contains( innerPath ) ) {
									moddedItems.add( innerPath );
								}
							}
						}
						else if ( fileName.endsWith( ".xml.rawclobber" ) || fileName.endsWith( ".rawclobber.xml" ) ) {
							innerPath = parentPath + fileName.replaceAll( "[.](?:xml[.]rawclobber|rawclobber[.]xml)$", ".xml" );
							innerPath = checkCase( innerPath, knownPaths, knownPathsLower );

							log.warn( String.format( "Copying xml as raw text: %s", innerPath ) );

							// Normalize line endings to CR-LF.
							//   decodeText() reads anything and returns an LF string.
							String fixedText = ModUtilities.decodeText( zis, modFile.getName()+":"+parentPath+fileName ).text;
							fixedText = Pattern.compile("\n").matcher( fixedText ).replaceAll( "\r\n" );

							InputStream fixedStream = ModUtilities.encodeText( fixedText, ultimateEncoding, modFile.getName()+":"+parentPath+fileName+" (with new EOL)" );

							if ( !moddedItems.contains( innerPath ) ) {
								moddedItems.add( innerPath );
							} else {
								log.warn( String.format( "Clobbering earlier mods: %s", innerPath ) );
							}

							if ( pack.contains( innerPath ) )
								pack.remove( innerPath );
							if ( fileName.startsWith( "text_misc." ) || fileName.startsWith( "misc." ) ) {
								InputStream customStream = getClass().getResourceAsStream( "/" + slipstreamIdentifierResource );
								if ( customStream != null ) {
									InputStream finalStream = ModUtilities.appendXMLFile(
											fixedStream, customStream, ultimateEncoding,
											modFile.getName() + ":" + parentPath + fileName,
											"slipstream-self-metadata:" + slipstreamIdentifierResource
									);
									customStream.close();
									fixedStream = finalStream;
								}
								else {
									warnLogMetadataNotFound();
								}
							}
							pack.add( innerPath, fixedStream );
						}
						else if ( fileName.endsWith( ".xml" ) ) {
							innerPath = checkCase( innerPath, knownPaths, knownPathsLower );

							InputStream fixedStream = ModUtilities.rebuildXMLFile( zis, ultimateEncoding, modFile.getName()+":"+parentPath+fileName, false );

							if ( !moddedItems.contains( innerPath ) ) {
								moddedItems.add( innerPath );
							} else {
								log.warn( String.format( "Clobbering earlier mods: %s", innerPath ) );
							}

							if ( pack.contains( innerPath ) )
								pack.remove( innerPath );
							if ( fileName.equals( "text_misc.xml" ) || fileName.equals( "misc.xml" ) ) {
								InputStream customStream = getClass().getResourceAsStream( "/" + slipstreamIdentifierResource );
								if ( customStream != null ) {
									InputStream finalStream = ModUtilities.appendXMLFile(
											fixedStream, customStream, ultimateEncoding,
											modFile.getName() + ":" + parentPath + fileName,
											"slipstream-self-metadata:" + slipstreamIdentifierResource
									);
									customStream.close();
									fixedStream = finalStream;
								}
								else {
									warnLogMetadataNotFound();
								}
							}
							pack.add( innerPath, fixedStream );
						}
						else if ( fileName.endsWith( ".xsl" ) ) {
							innerPath = checkCase( innerPath, knownPaths, knownPathsLower );

							if ( pack.contains( innerPath ) ) {
								log.warn( "Clobbering earlier stylesheet: " + innerPath );
								pack.remove( innerPath );
							}
							pack.add( innerPath, zis );
							//log.info( "Added stylesheet to dat: " + innerPath );

							if ( !moddedItems.contains( innerPath ) ) {
								moddedItems.add( innerPath );
							}
						}
						else if ( fileName.endsWith( ".txt" ) ) {
							innerPath = checkCase( innerPath, knownPaths, knownPathsLower );

							// Normalize line endings for other text files to CR-LF.
							//   decodeText() reads anything and returns an LF string.
							String fixedText = ModUtilities.decodeText( zis, modFile.getName()+":"+parentPath+fileName ).text;
							fixedText = Pattern.compile("\n").matcher( fixedText ).replaceAll( "\r\n" );

							InputStream fixedStream = ModUtilities.encodeText( fixedText, ultimateEncoding, modFile.getName()+":"+parentPath+fileName+" (with new EOL)" );

							if ( !moddedItems.contains( innerPath ) ) {
								moddedItems.add( innerPath );
							} else {
								log.warn( String.format( "Clobbering earlier mods: %s", innerPath ) );
							}

							if ( pack.contains( innerPath ) )
								pack.remove( innerPath );
							pack.add( innerPath, fixedStream );
						}
						else {
							innerPath = checkCase( innerPath, knownPaths, knownPathsLower );

							if ( !moddedItems.contains( innerPath ) ) {
								moddedItems.add( innerPath );
							} else {
								log.warn( String.format( "Clobbering earlier mods: %s", innerPath ) );
							}

							if ( pack.contains( innerPath ) )
								pack.remove( innerPath );
							pack.add( innerPath, zis );
						}

						zis.closeEntry();
					}
				}
				finally {
					try {if ( zis != null ) zis.close();}
					catch ( Exception e ) {}

					try {if ( fis != null ) fis.close();}
					catch ( Exception e ) {}

					System.gc();
				}

				if ( modFile.equals( selfMetadataMod ) ) {
					continue;
				}
				else {
					observer.patchingMod( modFile );
				}
				// same form as above
				fis = null;
				zis = null;
				try {
					fis = new FileInputStream( modFile );
					zis = new ZipInputStream( new BufferedInputStream( fis ) );
					ZipEntry item;
					while ( (item = zis.getNextEntry()) != null ) {
						if ( item.isDirectory() ) {
							zis.closeEntry();
							continue;
						}
						String innerPath = item.getName();
						innerPath = innerPath.replace( '\\', '/' );  // Non-standard zips.
						Matcher m = pathPtn.matcher( innerPath );
						if ( !m.matches() ) {
							// "Unexpected innerPath" warning already shown above
							zis.closeEntry();
							continue;
						}
						String parentPath = m.group( 1 );
						String root = m.group( 2 );
						String fileName = m.group( 3 );
						AbstractPack pack = packContainer.getPackFor( innerPath );
						if ( pack == null || ModUtilities.isJunkFile( innerPath ) ) {
							// "Unexpected innerPath" "Ignoring innerPath with known root" "Skipping junk file"
							// these warnings are already shown above
							zis.closeEntry();
							continue;
						}
						if ( fileName.endsWith( ".xsl" ) ) {
							log.info( "" );
							innerPath = parentPath + fileName.replaceAll( "[.]xsl$", ".xml" );
							innerPath = checkCase( innerPath, knownPaths, knownPathsLower );
							if ( pack.contains( innerPath ) ) {
								log.info( String.format( "Transforming file: %s", innerPath ) );
								InputStream mainStream = null;
								try {
									mainStream = pack.getInputStream( innerPath );
									// CloseShieldInputStream prevents ModUtilities.transformDocument from auto-closing zis
									InputStream transformedStream = ModUtilities.transformXMLFile( mainStream, CloseShieldInputStream.wrap(zis), ultimateEncoding, pack.getName()+":"+innerPath, modFile.getName()+":"+parentPath+fileName, pack );
									mainStream.close();
									pack.remove( innerPath );
									pack.add( innerPath, transformedStream );
								}
								finally {
									try {if ( mainStream != null ) mainStream.close();}
									catch ( IOException e ) {}
								}

								if ( !moddedItems.contains( innerPath ) ) {
									moddedItems.add( innerPath );
								}
							}
							else {
								String padding = new String( new char[23] ).replace("\0", " ");
								log.warn( String.format( "Could not find base file: %s\n%sAssuming %s is an XSL library", innerPath, padding, fileName ) );
							}
						}
						// copied from below
						zis.closeEntry();
					}
				}
				// copied from above
				finally {
					try {if ( zis != null ) zis.close();}
					catch ( Exception e ) {}

					try {if ( fis != null ) fis.close();}
					catch ( Exception e ) {}

					System.gc();
				}

				modsInstalled++;
				observer.patchingProgress( progMilestone + progModsMax/modFiles.size()*modsInstalled, progMax );
			}
			// Remove the temporary file
			if ( selfMetadataMod != null ) {
				try {
					Files.deleteIfExists( selfMetadataMod.toPath() );
				}
				catch ( IOException e ) {
					log.info( "" );
					log.warn( String.format( "Couldn't delete %s, located in %s.", selfMetadataMod.getName(), selfMetadataMod.getParentFile() ) );
					log.info( "This mod file is created during patching to add metadata, after which it is no longer needed and deleted." );
					log.info( "Modders can then reference this metadata to guarantee the end user uses this custom version of Slipstream." );
					log.info( "" );
				}
			}

			progMilestone += progModsMax;
			observer.patchingProgress( progMilestone, progMax );

			// Prune 'removed' files from dats.
			for ( AbstractPack pack : packContainer.getPacks() ) {
				observer.patchingStatus( String.format( "Repacking \"%s\"...", pack.getName() ) );

				AbstractPack.RepackResult repackResult = pack.repack();
				if ( repackResult != null ) {
					long bytesChanged = repackResult.bytesChanged;
					log.info( String.format( "Repacked \"%s\" (%d bytes affected)", pack.getName(), bytesChanged ) );
				}

				datsRepacked++;
				observer.patchingProgress( progMilestone + progRepackMax/backedUpDats.size()*datsRepacked, progMax );
			}
			progMilestone += progRepackMax;
			observer.patchingProgress( progMilestone, progMax );

			observer.patchingProgress( 100, progMax );
			return true;
		}
		finally {
			if ( packContainer != null ) {
				for ( AbstractPack pack : packContainer.getPacks() ) {
					try {pack.close();}
					catch( Exception e ) {}
				}
			}
		}
	}

	private void warnLogMetadataNotFound() {
		log.warn( "Metadata that says this Slipstream is a custom version could not be retrieved from jar." );
		log.warn( "Mods that require this metadata will not patch. Please verify the jar is not corrupted." );
	}

	/**
	 * Checks if an innerPath exists, ignoring letter case.
	 *
	 * If there is no collision, the innerPath is added to the known lists.
	 * A warning will be logged if a path with differing case exists.
	 *
	 * @param knownPaths a list of innerPaths seen so far
	 * @param knownPathsLower a copy of knownPaths, lower-cased
	 * @return the existing path (if different), or innerPath
	 */
	private String checkCase( String innerPath, List<String> knownPaths, List<String> knownPathsLower ) {
		if ( knownPaths.contains( innerPath ) ) return innerPath;

		String lowerPath = innerPath.toLowerCase();
		int lowerIndex = knownPathsLower.indexOf( lowerPath );
		if ( lowerIndex != -1 ) {
			String knownPath = knownPaths.get( lowerIndex );
			log.warn( String.format( "Modded file's case doesn't match existing path: \"%s\" vs \"%s\"", innerPath, knownPath ) );
			return knownPath;
		}

		knownPaths.add( innerPath );
		knownPathsLower.add( lowerPath );
		return innerPath;
	}



	public static class BackedUpDat {
		public File datFile = null;
		public File bakFile = null;
	}
}
