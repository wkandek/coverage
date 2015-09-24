#!/usr/bin/perl

#
# coverage.pl - asset group coverage script
#
# v0.1
#
# 1. reads in a config file with AGs and daterange and OP name
# 2. gets data for all AGs and saves to disk in XML
# 3. parses AG XML and SCAN History XML and calculates scan coverage for the spec OP and date
#
# v0.1  - wkandek - inital version, copy from ag_sc.pl v1.0
# v0.1a - wkandek - supports now no OP in conf file 
#                   cleanup unused code
# v0.1b - eperraudeau/wkandek - trim function for single IP addresses that 
#         have spaces around them, also single header only in print
# v0.1c - wkandek - config file format sla and op moved into AG record
# v0.1d - wkandek - optimizations with empty IP ranges
# v0.1e - wkandek - deal with [...] indicator of cut off IPs 
#                   log now only when file exists, helps to turn logging
#                   on/off when running by moving file
# v0.1f - wkandek - support regex in OP string - add: .* for prefix matching 
# v0.1g - wkandek - bug in compute_Sr when range started with same IP address 


## Modules
use strict;
no strict 'subs';
use XML::Twig;           # XML manipulation library
use LWP;                 # retrieving data via HTTPS
use Getopt::Long;        # parses the option passed to the program
use Date::Parse;         # for date manipulation
use Time::Format;
use Socket;
use Data::Dumper;

##
my $DEBUG = 1;
my $INFO = 2;

my $ipc = 0;
## Variables
my $help;                                         # for help option
my $timeout = 600;                                # for timeout option
my $debug = 0;                                    # for debug option
my $verbose;                                      # for verbose option
my $nodownload;                                   # for nodownload option
my $onlydownload;                                 # for onlydownload option
my $configfile;                                   # for config option
my $syncfiles;                                    # for syncfiles option

my $scriptname = "coverage";                      # defines scriptname used for configfiles, browser id, etc
my $version = "v0.1g";                            # defines version
my $configfilename = $scriptname.".conf";         # configfile to use
my $verboselogfilename = $scriptname.".log";      # logfile to use
my $logidnumber = int( rand( 100000 ));           # log ID number - helps in correlating loglines

my %division;                                     # associative array to store the division of an ag
my %location;                                     # associative array to store the location of an ag
my %function;                                     # associative array to store the function of an ag
my %comment;                                      # associative array to store the comment of an ag
my %scandate;
my %scantarget;
my %optionprofile;

my $ips;
my $ag;
my $sla;
my $op;

my $username;
my $passwd;
my $pusername;
my $ppasswd;
my $apiurl;
my $proxyaddr;
my %agstocheck;
my %scansla;
my %op;

my $scanranges;
my $ipr;
my $ipstring;

my @agips;
my @scanips;
my @agips_initial;
my @endstate;



### Subroutines

## ----------------------------------------------------------------------
## usage
## prints short usage message if param --help is given to the program 
##
## @param arg1 - NONE
## ----------------------------------------------------------------------
sub usage() {
  print "Usage: $scriptname [OPTIONS]\n$version\n";
  print "--help - this message\n--timeout=nnnn  - set timeout to value is seconds\n";
  print "--config=name - use this configfile instead of default\n--verbose - log to logfile\n--debug - log more information to logfi
le\n";
  print "--syncfiles - skip download if XML files on disk exists\n";
  print "--nodownload - use XML files on disk for processing do not download from server\n--onlydownload - only download files from
server do not process\n";
  return( 1 );
}



## ----------------------------------------------------------------------
## printlog
## prints log messages to a file, depending on verbose setting on cmdline
## understands DEBUG and prints more info if DEBUG is set
##
## @param arg1 - level of logging verbosity
## @param arg2..x - logmessage(s)
## ----------------------------------------------------------------------
sub printlog( @ ) {
  my $level = shift( @_ );

  
  if (( $level == $DEBUG )) {
    if ( $debug ) {
      if ( -e $verboselogfilename ) {
        open( LOGFILE, ">>$verboselogfilename" ) || die "$scriptname: Logfile $verboselogfilename could not be opened\n";
        print LOGFILE localtime( time()).":$scriptname:$logidnumber:$level:@_\n";
        close( LOGFILE );
      }
    }
  }
  else {
    if ( $verbose ) {
      if ( -e $verboselogfilename ) {
        open( LOGFILE, ">>$verboselogfilename" ) || die "$scriptname: Logfile $verboselogfilename could not be opened\n";
        print LOGFILE localtime( time()).":$scriptname:$logidnumber:$level:@_\n";
        close( LOGFILE )
      }
    }
  }
}


## ----------------------------------------------------------------------
## confextract
## populates the internal filters from the XML twig
## has default values for all filters - type, severity, startdate, enddate
## mandatory: user/pass, URL, AGs
## optional: Proxy, dynamic columns
##
## @param arg1 - root
## @param arg2 - twig
## ----------------------------------------------------------------------
sub confextract
{
  my @ags;
  my $ag;
  my $agname;
  my( $twig, $config)= @_;

  
  $username = $config->first_child("USERNAME")->text;
  $passwd = $config->first_child("PASSWORD")->text;
  $apiurl = $config->first_child("URL")->text;
  if ( $config->first_child("PROXY")) {
    $proxyaddr = $config->first_child("PROXY")->text;
  }
  if ( $config->first_child("PROXYUSERNAME")) {
    $pusername = $config->first_child("PROXYUSERNAME")->text;
    $ppasswd = $config->first_child("PROXYPASSWORD")->text;
  }
  @ags = $config->first_child("AGLIST")->children;
  foreach $ag (@ags) {
    if ( $ag->tag eq "AG" ) {
      $agname = $ag->text;
      $agstocheck{$agname} = 1;
      if ( $ag->att('scansla')) {
        $scansla{$agname} = $ag->att('scansla');
      }
      if ( $ag->att('op')) {
        $op{$agname} = $ag->att('op');
      }
    }
  }
  
  $twig->purge;                             # delete the twig so far
}


## ----------------------------------------------------------------------
## read_config
## reads in config file and sets up handler for XML twig
##
## @param arg1 - filename
## ----------------------------------------------------------------------
sub read_config( $ ) {
  my $filename;

  
  $filename = shift( @_ );
  if ( $filename eq "" ) {
    $filename = $configfilename;
  }
  # create the twig
  my $twig= new XML::Twig( twig_handlers => { COVERAGECONFIG => \&confextract } );

  # parse the twig
  $twig->safe_parsefile( $filename ) || die "$scriptname: Config $filename file error: $@";
}


## ----------------------------------------------------------------------
## agextract
## populates the internal ag structure from the XML twig
##
## @param arg1 - root
## @param arg2 - twig
## ----------------------------------------------------------------------
sub agextract
{
  my( $twig, $ag)= @_;
  my $agname;
  my $scanips;
  my @ipranges;
  my $iprange;
  my $agcounter;
  
  
  $agname = $ag->first_child("TITLE")->text;
  if ( $ag->first_child("LOCATION")) {
    $location{$agname} = $ag->first_child("LOCATION")->text;
  }
  if ( $ag->first_child("FUNCTION")) {
    $function{$agname} = $ag->first_child("FUNCTION")->text;
  }
  if ( $ag->first_child("DIVISION")) {
    $division{$agname} = $ag->first_child("DIVISION")->text;
  }
  if ( $ag->first_child("COMMENT")) {
    $comment{$agname} = $ag->first_child("COMMENT")->text;
  }
  if ( $ag->first_child("SCANIPS" )) {
    $scanips = $ag->first_child("SCANIPS" );
    @ipranges = $scanips->children;
    $agcounter = 0;
    foreach $iprange (@ipranges) {
      $ips->{$agname}->{$agcounter} = $iprange->text;
      $agcounter++;
    }
  }
  $twig->purge;                             # delete the twig so far
}


## ----------------------------------------------------------------------
## parse_ag_file
## parses the AG file and populates internal structures via XML twig
##
## @param arg1 - NONE
## ----------------------------------------------------------------------
sub parse_ag_file() {

  # create the twig
  my $twig= new XML::Twig( twig_handlers => { ASSET_GROUP => \&agextract } );

  # parse the twig
  $twig->safe_parsefile( "ag.xml" ) || die "$scriptname: ag.xml file error: $@";
}


## ----------------------------------------------------------------------
## shextract
## populates the internal sh structure from the XML twig
##
## @param arg1 - root
## @param arg2 - twig
## ----------------------------------------------------------------------
sub shextract
{
  my( $twig, $sr )= @_;
  my $scanref;
  my $op;
  
  
  $scanref = $sr->att('ref');
  $scandate{$scanref} = $sr->att('date');
  $scantarget{$scanref} = $sr->att('target');
  if ( $sr->first_child("OPTION_PROFILE")) {
    $op = $sr->first_child("OPTION_PROFILE" );
    if ( $op->first_child("OPTION_PROFILE_TITLE")) {
      $optionprofile{$scanref} = $op->first_child("OPTION_PROFILE_TITLE")->text;
      printlog $DEBUG, "shextract: ".$op->first_child("OPTION_PROFILE_TITLE")->text;
#      printlog $DEBUG, "shextract: ".$scantarget{$scanref};
    }
  }
  $twig->purge;                             # delete the twig so far
}


## ----------------------------------------------------------------------
## parse_sh_file
## parses the scan_report_list file and populates internal structures via XML twig
##
## @param arg1 - NONE
## ----------------------------------------------------------------------
sub parse_sh_file() {

  # create the twig
  my $twig= new XML::Twig( twig_handlers => { SCAN_REPORT => \&shextract } );

  # parse the twig
  $twig->safe_parsefile( "sh.xml" ) || die "$scriptname: sh.xml file error: $@";
}

## ----------------------------------------------------------------------
## compute_sr_ranges
##
## @param arg1 -  AG name
## @param arg2 -  day range to include
## @param arg3 - OP to use
## ----------------------------------------------------------------------
sub compute_sr_ranges( @ ) {
  my $agname = shift( @_ );
  my $day = shift( @_ );
  my $op = shift( @_ );

  my $sr;
  my $now;
  my $cutoff;
  my @st;
  my $ste;
  my $ipr;
  my $ipstring;
  my %iprange;
  my %ipnum;
  my $ag_s;
  my $ag_si;
  my $ag_e;
  my $ag_ei;


  $now = time(); 
  $cutoff = $now - $day * 24*60*60;
  # go over all scan requests
  foreach $sr (keys %scandate) {
    printlog $DEBUG, "compute_sr_ranges: parameters $agname $sr $day $op ";
    # is it the OP that we are looking for
    printlog $DEBUG, "compute_sr_ranges: $sr $day $op OP ".$optionprofile{$sr};
    if ( $optionprofile{$sr} =~ m/^$op$/ || length($op) == 0 ) {
      # is it within the date range
      printlog $DEBUG, "compute_sr_ranges: OP match $sr $day $op cutoff $cutoff ".str2time($scandate{$sr})." ".$scandate{$sr};
      if ( str2time($scandate{$sr}) > $cutoff ) {
        # break string into individual ranges to dedupe array
        printlog $DEBUG, "compute_sr_ranges: Scan applicable: $agname, $sr, ".$optionprofile{$sr}.", ".$scandate{$sr}.", ".$scantarget{$sr};
        @st = split( /,/, $scantarget{$sr} );
        foreach $ste (@st) {
          if ( $ste =~ m/\[/ ) {
            printlog $DEBUG, "compute_sr_ranges: st loop OVERFLOW";
          } 
          else {
            $iprange{$ste} = 1;
            printlog $DEBUG, "compute_sr_ranges: st loop $ste";
          }
        }  
      }
    }
  } 

  # order IPs
  foreach $ipr (keys %iprange) {
    if ( $ipr =~ m/53.79.105\[/ ) {
      $ipr = $ipr;
    }
    if ( $ipr =~ m/([0-9\.]+)\-/ ) {
      $ag_s = trim($1);
      if ( $ipr =~ m/\-([0-9\.]+)/ ) {
        $ag_e = trim($1);
        $ag_ei = unpack "N", inet_aton( $ag_s );
      }
    }
    else {
      $ag_s = trim($ipr);
      $ag_e = "";
      $ag_ei = 0;
    } 
    if ( $ag_si = unpack "N", inet_aton( $ag_s )) {
      $ipnum{$ag_si*$ag_ei} = $ipr;
    }
  }
  # assemble string with de duped IPs
  $ipstring = "";
  foreach $ipr ( sort keys %ipnum) {
    $ipstring .= $ipnum{$ipr}.",";
  }
  if ( length( $ipstring ) > 0 ) {
    $ipstring = substr( $ipstring, 0, length($ipstring)-1);
  }
  return( $ipstring );
}


## ----------------------------------------------------------------------
## get_ag_file
## retrieves the AG defintions for the account and saves to file
##
## @param arg1 - NONE
## ----------------------------------------------------------------------
sub get_ag_file() {
  my $url;
  my $browser;
  my $starttime;
  my $endtime;
  my $response;
  my $content;


  $url = "https://$apiurl/msp/asset_group_list.php";

  $browser = LWP::UserAgent->new;
  $browser->credentials(
    $apiurl.':443',
    'MSP Front Office',
    $username => $passwd
  );
  $browser->agent("libwww - ".$scriptname." ".$version);
  $browser->timeout( $timeout );

  if ( $proxyaddr ) {
    printlog $INFO,  "Proxy defined: $proxyaddr";
    $ENV{'HTTPS_PROXY'} = $proxyaddr;
    if ( $pusername ) {
      printlog $INFO,  "ProxyUser defined: $pusername $ppasswd";
      $ENV{'HTTPS_PROXY_USERNAME'} = $pusername;
      $ENV{'HTTPS_PROXY_PASSWORD'} = $ppasswd;
    }
  }
  printlog $INFO,  "$url";
  $starttime = time();
  $response = $browser->get($url);

  if ( !($response->is_success)) {
    printlog $INFO, "$scriptname: Error at $url ".$response->status_line." Aborting";
    die "$scriptname: Error at $url ".$response->status_line." Aborting";
  }
  $endtime = time();
  printlog $INFO,  "  ".$endtime-$starttime." seconds - size: ".length($response->content);

  $content = $response->content;
  open( XMLOUT, ">ag.xml" );
  print XMLOUT $content;
  close( XMLOUT );

  if ( $response->content =~ m/(\<ERROR.*\<\/ERROR\>)/ ) {
    printlog $INFO, "$scriptname: Reportfile $url reported error: $1";
    die "$scriptname: Reportfile $url reported error: $1";
  }
}


## ----------------------------------------------------------------------
## get_sh_file
## retrieves Scan_history for the account and saves to file
##
## @param arg1 - NONE
## ----------------------------------------------------------------------
sub get_sh_file() {
  my $url;
  my $browser;
  my $starttime;
  my $endtime;
  my $response;
  my $content;


  $url = "https://$apiurl/msp/scan_report_list.php";

  $browser = LWP::UserAgent->new;
  $browser->credentials(
    $apiurl.':443',
    'MSP Front Office',
    $username => $passwd
  );
  $browser->agent("libwww - ".$scriptname." ".$version);
  $browser->timeout( $timeout );

  if ( $proxyaddr ) {
    printlog $INFO,  "Proxy defined: $proxyaddr";
    $ENV{'HTTPS_PROXY'} = $proxyaddr;
    if ( $pusername ) {
      printlog $INFO,  "ProxyUser defined: $pusername $ppasswd";
      $ENV{'HTTPS_PROXY_USERNAME'} = $pusername;
      $ENV{'HTTPS_PROXY_PASSWORD'} = $ppasswd;
    }
  }
  printlog $INFO,  "$url";
  $starttime = time();
  $response = $browser->get($url);

  if ( !($response->is_success)) {
    printlog $INFO, "$scriptname: Error at $url ".$response->status_line." Aborting";
    die "$scriptname: Error at $url ".$response->status_line." Aborting";
  }
  $endtime = time();
  printlog $INFO,  "  ".$endtime-$starttime." seconds - size: ".length($response->content);

  $content = $response->content;
  open( XMLOUT, ">sh.xml" );
  print XMLOUT $content;
  close( XMLOUT );

  if ( $response->content =~ m/(\<ERROR.*\<\/ERROR\>)/ ) {
    printlog $INFO, "$scriptname: Reportfile $url reported error: $1";
    die "$scriptname: Reportfile $url reported error: $1";
  }
}


## ----------------------------------------------------------------------
## trim 
## removes blanks from string
##
## @param arg1 - string 
## ----------------------------------------------------------------------
sub trim($)
{
  my $string = shift;
  $string =~ s/^\s+//;
  $string =~ s/\s+$//;
  return $string;
}


## ----------------------------------------------------------------------
## DecIP 
## decrements an IP, skips .0
##
## @param arg1 - IP in string format
## ----------------------------------------------------------------------
sub DecIP($)
{
  my $ip_i;
  my $ip;

  $ip_i = $_[0];
  $ip_i--;
  $ip = inet_ntoa( pack "N", $ip_i );
  if ( $ip =~ m/\.0$/ ) {
    $ip_i--;
    # $ip = inet_ntoa( pack "N", $ip_i );
    # print "$ip .0 found \n";
  }
  return($ip_i);
}


## ----------------------------------------------------------------------
## IncIP 
## Increments an IP, skips .0
##
## @param arg1 - IP in string format
## ----------------------------------------------------------------------
sub IncIP($)
{
  my $ip_i;
  my $ip;

  $ip_i = $_[0];
  $ip_i++;
  $ip = inet_ntoa( pack "N", $ip_i );
  if ( $ip =~ m/\.0$/ ) {
    $ip_i++;
    # $ip = inet_ntoa( pack "N", $ip_i );
    # print "$ip .0 found \n";
  }
  return($ip_i);
}


## ----------------------------------------------------------------------
## CalcCoverage 
## Calculates the coverage (overlap) of argument aan array of IPs
## over argument1 an array of IPs as well
##
## @param arg1 - array of IPs in string format
## @param arg2 - array of IPs in string format
## ----------------------------------------------------------------------
sub CalcCoverage( @@ )
{
  my @agip;
  my @scanip;

  # AG IP start/end in text and int
  my $ag_s;
  my $ag_si;
  my $ag_e;
  my $ag_ei;

  # AG line read 
  my $ag_le;

  # Scan Request start/end in text and int
  my $sr_s;
  my $sr_si;
  my $sr_e;
  my $sr_ei;

  # Scan Request line read
  my $sr_le;

  # Contain the new AG ranges when splits, etc are necessary
  my $new_agr;
  my $new2_agr;

  # to maintain the list of Ranges to check and to print final results
  my $ag_len;
  my $ag_count;
  my $ip_max;


  printlog $INFO, "Start calccoverage";
  @agip = @{$_[0]};
  @scanip = @{$_[1]};
  $ag_len = scalar @agip;
  $ag_count = 0;
  $ip_max = unpack "N", inet_aton( "255.255.255.255" );

  # loop over al Ranges
  foreach $ag_le (@agip) {
    # is there a range, could be deleted
    if ( length( $ag_le ) > 0 ) {
      # split into start and end - is there a dash ? if not is it the same IP
      if ( $ag_le =~ m/([0-9\.]+)\-/ ) {
        $ag_s = $1;
        if ( $ag_le =~ m/\-([0-9\.]+)/ ) {
          $ag_e = $1;
        }
      } else {
        $ag_s = trim($ag_le);
        $ag_e = trim($ag_le);
      }
      $ag_si = unpack "N", inet_aton( $ag_s );
      $ag_ei = unpack "N", inet_aton( $ag_e );

      # debug prints
      printlog $DEBUG, "calccoverage: Target match AG range $ag_le $ag_s - $ag_e, $ag_si - $ag_ei"; 

      # loop over all scan requests
      my $src = 0;
      foreach $sr_le (@scanip) {
        $src++;
        # split into start end end, dash or single IP
        if ( $sr_le =~ m/([0-9\.]+)\-/ ) {
          $sr_s = $1;
          if ( $sr_le =~ m/\-([0-9\.]+)/ ) {
            $sr_e = $1;
          }
        }
        else {
          $sr_s = trim($sr_le);
          $sr_e = trim($sr_le);
        }
        $sr_si = unpack "N", inet_aton( $sr_s );
        $sr_ei = unpack "N", inet_aton( $sr_e );

        # debug print
        printlog $DEBUG, "calccoverage: about to match AG $ag_s - $ag_e $ag_si - $ag_ei $src R $sr_s - $sr_e  $sr_si - $sr_ei"; 

        # 4 cases, bigger, smaller, overlap front, overlap end
        if (( $sr_si <= $ag_si ) && ( $sr_ei >= $ag_ei )) {
          # range is bigger - delete range and we are done with the loop
          printlog $DEBUG, "calccoverage: match - range scanned is bigger - delete ag range"; 
          $agip[$ag_count] = "";
          $ag_si = $ip_max;
          $ag_ei = 0;
          $ag_s = "255.255.255.255";
          $ag_e = "0.0.0.0";
        }
        elsif (( $sr_si > $ag_si ) && ( $sr_ei < $ag_ei )) {
          # range is smaller break in two, add 2 entry at end
          # delete current and 
          $sr_si = DecIP($sr_si);
          $new_agr = inet_ntoa( pack "N", $ag_si )."-".inet_ntoa( pack "N", $sr_si ); 
          $sr_ei = IncIP($sr_ei);
          $new2_agr = inet_ntoa( pack "N", $sr_ei )."-".inet_ntoa( pack "N", $ag_ei ); 
          # add 2 new range to end of list 
          $agip[$ag_len] = $new_agr;
          $ag_len++;
          $agip[$ag_len] = $new2_agr; 
          $ag_len++;
    
          # adjust int reps to releflect new reality
          $agip[$ag_count] = "";
          $ag_si = $ip_max;
          $ag_ei = 0;
          $ag_s = "255.255.255.255";
          $ag_e = "0.0.0.0";
    
          printlog $DEBUG, "calccoverage: match - range is smaller, breaks in two, modified: $new_agr new: $new2_agr"; 
        }
        elsif (( $sr_si <= $ag_si ) && ( $sr_ei >= $ag_si ) && ( $sr_ei < $ag_ei )) {
          # range overlaps front 
          $sr_ei = IncIP($sr_ei);
          $new_agr = inet_ntoa( pack "N", $sr_ei )."-".inet_ntoa( pack "N", $ag_ei ); 
          $agip[$ag_len] = $new_agr;
          $ag_len++;

          # adjust int reps to reflect new reality
          $agip[$ag_count] = "";
          $ag_si = $ip_max;
          $ag_ei = 0;
          $ag_s = "255.255.255.255";
          $ag_e = "0.0.0.0";

          printlog $DEBUG, "calccoverage: match range overlaps front modified: $new_agr"; 
        }
        elsif (( $sr_si <= $ag_ei ) && ( $sr_si > $ag_si ) && ( $sr_ei >= $ag_ei )) {
          $sr_si = DecIP($sr_si);
          $new_agr = inet_ntoa( pack "N", $ag_si )."-".inet_ntoa( pack "N", $sr_si ); 
          $agip[$ag_len] = $new_agr;
          $ag_len++;

          # adjust int reps to reflect new reality
          $agip[$ag_count] = "";
          $ag_si = $ip_max;
          $ag_ei = 0;
          $ag_s = "255.255.255.255";
          $ag_e = "0.0.0.0";
    
          printlog $DEBUG, "calccoverage: match range overlap back modified: $new_agr"; 
        }
        else {
          printlog $DEBUG, "calccoverage: no match"; 
        }
      }
      printlog $INFO, "calccoverage: match end $src";
    }
    else {
      printlog $DEBUG, "calccoverage: empty AGLE"; 
    }
    $ag_count++;

    # debug prints
    printlog $DEBUG, "calccoverage: State now: start";  
    my $agc = 0;
    foreach $ag_le (@agip) { 
      $agc++;
      printlog $DEBUG, "calccoverage: State now: $agc $ag_le";
    } 
    printlog $DEBUG, "calccoverage: State now: end"; 
    if ( $agc % 100 eq 0 ) {
      $agc = 0;
      foreach $ag_le (@agip) { 
        $agc++;
        printlog $INFO, "calccoverage: State now: $agc $ag_le";
      } 
    }
    printlog $INFO, "calccoverage: State end $agc"; 
  }
  return( @agip );
}


sub print_results( $$$ )
{
  my $ag;
  my $sla;
  my $op;
  my $ag_le;
  my $ag_si;
  my $ag_ei;
  my $coverage;
  my $init_coverage;
  my $end_coverage;
  my $printstring;


  # End state
  $ag = shift;
  $sla = shift;
  $op = shift;
#  print "Asset Group, Divison, Function, Location, Comment, SLA, Option Profile,Coverage\n";
  print "$ag,".$division{$ag}.",".$function{$ag}.",".$location{$ag}.",".$comment{$ag}.",$sla,$op,";

  $printstring = "  Initial Network:\n";

  $init_coverage = 0;
  foreach $ag_le (@agips_initial) {
    if ( $ag_le =~ m/([0-9\.]+)\-/ ) {
      $ag_si = unpack "N", inet_aton( $1 );
      if ( $ag_le =~ m/\-([0-9\.]+)/ ) {
        $ag_ei = unpack "N", inet_aton( $1 );
      }
    }
    else {
      $ag_si = unpack "N", inet_aton( $ag_le );
      $ag_ei = unpack "N", inet_aton( $ag_le );
    }
    $init_coverage += $ag_ei - $ag_si + 1;
    $printstring .=  "    Network: ".$ag_le." ".$init_coverage." IPs\n";
  }
  $printstring .= "  End Network:\n";
  foreach $ag_le (@endstate) {
    if ( length( $ag_le ) > 0 ) {
      if ( $ag_le =~ m/([0-9\.]+)\-/ ) {
        $ag_si = unpack "N", inet_aton( $1 );
        if ( $ag_le =~ m/\-([0-9\.]+)/ ) {
          $ag_ei = unpack "N", inet_aton( $1 );
        }
      }
      else {
        $ag_si = unpack "N", inet_aton( $ag_le );
        $ag_ei = unpack "N", inet_aton( $ag_le );
      }
      $coverage = $ag_ei - $ag_si + 1;
      $end_coverage += $coverage;
      $printstring .= "    Network: ".$ag_le." Coverage Missing: ".$coverage." IPs\n";
    }
  }
#  print 100-$end_coverage/$init_coverage*100;
  printf( "%.2f", 1-$end_coverage/$init_coverage );
  print "\n";

  if ( $verbose ) {
    print $printstring;
  }
}


sub print_splunk( $$$ )
{
  my $ag;
  my $sla;
  my $op;
  my $ag_le;
  my $ag_si;
  my $ag_ei;
  my $coverage;
  my $init_coverage;
  my $end_coverage;


  # End state
  $ag = shift;
  $sla = shift;
  $op = shift;

  $init_coverage = 0;
  foreach $ag_le (@agips_initial) {
    if ( $ag_le =~ m/([0-9\.]+)\-/ ) {
      $ag_si = unpack "N", inet_aton( $1 );
      if ( $ag_le =~ m/\-([0-9\.]+)/ ) {
        $ag_ei = unpack "N", inet_aton( $1 );
      }
    }
    else {
      $ag_si = unpack "N", inet_aton( $ag_le );
      $ag_ei = unpack "N", inet_aton( $ag_le );
    }
    $init_coverage += $ag_ei - $ag_si + 1;
  }
  foreach $ag_le (@endstate) {
    if ( length( $ag_le ) > 0 ) {
      if ( $ag_le =~ m/([0-9\.]+)\-/ ) {
        $ag_si = unpack "N", inet_aton( $1 );
        if ( $ag_le =~ m/\-([0-9\.]+)/ ) {
          $ag_ei = unpack "N", inet_aton( $1 );
        }
      }
      else {
        $ag_si = unpack "N", inet_aton( $ag_le );
        $ag_ei = unpack "N", inet_aton( $ag_le );
      }
      $coverage = $ag_ei - $ag_si + 1;
      $end_coverage += $coverage;
    }
  }
#  print 100-$end_coverage/$init_coverage*100;
  print "qgreportdate=".$time{"yyyy-mm-ddTh:mm:ss", time()}." ";
  print "qgag=$ag qgsla=$sla ";
  if ( $op eq "" ) {
    print "qgop=NA ";
  }
  else {
    print "qgop=$op ";
  }
  printf( "qgcoverage=%.2f", 1-$end_coverage/$init_coverage );
  print "\n";
}


## main
GetOptions( "config=s"=>\$configfile,"verbose"=>\$verbose, 
            "syncfiles"=>\$syncfiles, "debug"=>\$debug, 
            "timeout=s"=>\$timeout, "help"=>\$help,
            "nodownload"=>\$nodownload, "onlydownload"=>\$onlydownload );

$verbose && print "Start run: $version ".localtime(time())."\n";
printlog $INFO, "Start run";

$help && usage() && exit;

read_config($configfile);
$verbose && print "Parameters: not done yet\n";
printlog $INFO, "Parameters: ";

if ( $nodownload == 0 ) {
  $verbose && print "Getting AG file\n";
  get_ag_file();
  $verbose && print "Getting Scan History file\n";
  get_sh_file();
  parse_ag_file();
  parse_sh_file();
} 
else {
  parse_ag_file();
  parse_sh_file();
} 

print "Asset Group, Divison, Function, Location, Comment, SLA, Option Profile,Coverage\n";
# calc one AG - by hand needs a loop over the AGs in AG.xml
foreach $ag (sort keys %agstocheck) {

  if ( $ips->{$ag} ) {
    printlog $INFO, "Print Results - ag loop $ag";
    $sla = $scansla{$ag};
    $op = $op{$ag};
  
    # assemble the IP string
    $ipstring = "";
    foreach $ipr (keys %{$ips->{$ag}}) {
      $ipstring .= $ips->{$ag}->{$ipr}.",";
    }
    if ( length( $ipstring ) > 0 ) {
      $ipstring = substr( $ipstring, 0, length($ipstring)-1 );
    }
    @agips = split( /,/, $ipstring ); 
    @agips_initial = @agips;
    printlog $INFO, "Print Results - Compute SR $ag";
    $scanranges = compute_sr_ranges( $ag, $sla, $op );
    printlog $DEBUG, "Scan Ranges: $scanranges";
    @scanips = split( /,/, $scanranges );
    printlog $INFO, "Print Results - CalcCoverage $ag";
    @endstate = CalcCoverage( \@agips, \@scanips );

    print_splunk( $ag, $sla, $op );
  }
  else {
    print "AG $ag not found\n";
  }
}

$verbose && print "End run: ".localtime(time())."\n";
# printlog $INFO, "End run";
