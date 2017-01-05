#!/usr/bin/perl -w
# SIP Call Notifier
# (c) Piotr Oniszczuk
#
# 1.01 Changed Caller ID Name parsing to allow for no name.
#      by Larry Silverman
# 1.02 Reformat phone number to be in format xxx-xxx-xxxx.
#      Enable display of date/time in OSD.
#      Adjust default filter to check port 5060.
#      Reformat perl code.
#      by Kevin Venkiteswaran
# 1.03 Change reformat number (line 289) from xxx-xxx-xxxx to the
#      formats dependent on network type (mobile or other).
#      For numbers begining with 050, 051, 060, 066, 069
#      formating is xxxx-xxx-xxx. For rest is xxx-xxx-xx-xx.
#      By Lech Najdek/Piotr Oniszczuk
# 1.1  Adding telnet remote control for pausing frontends
#      when call is discovered. By Piotr Oniszczuk.
# 1.11 Adding checking for SIP messages duplicates. If received
#      silently dumped. By Piotr Oniszczuk.
# 1.12 SIP INVITE fields FROM and TO are separatelly parsed and sent
#      as FROM and TO in OSD notify container. By Piotr Oniszczuk.
# 1.13 OSD_notify container is sent twice for avoiding FE crash when non-complete
#      container reeived by FE. By Piotr Oniszczuk.
# 1.14 Checking if other than mobile num tel has leading 0.
#      If so, displayig it as xxx-xxx-xx-xx
# 1.15 Added sanity fuction limiting to 16 chars and filtering non-ascii chars
#      in caller[calling]numbers. By Piotr Oniszczuk.
# 1.2  Added multiple FE suport and resume FE after call ending.
#      By Piotr Oniszczuk.
# 1.3  Added multiple INVITE support (i.e when calling is BUSY). First INVITE
#      msg will notify OSD and telnet for pause, all consecutive will only notify OSD
#      and only BYE from last INVITE will telnet for resume.
#      By Piotr Oniszczuk.
# 1.4  Added checking FE state when call ends. If FE is paused then resume. If
#      FE is playing/idle (user resume/exit durring call) then not resume when
#      call ends. By Piotr Oniszczuk.
# 1.41 Speedup by adding threads for OSD & Telent actions
# 1.5  Adding watchdog for lacking BYE,ACK or CANCEL after INVITE.
#      In such cases watchgod will reset state machine to default
#      state. By Piotr Oniszczuk.
# 1.6  Adding OSD notification when call ends
# 1.7  Adding handling ACK & CANCEL msgs. ACK will kill housekeeping thread. CANCEL will
#      also resume playback and/or notify via OSD. By Piotr Oniszczuk.
# 1.71 Clenup debug messages
# 1.72 Remove monitoring ACK msgs
# 1.73 Minor bugfixing (remove $callid local declarations)
# 1.80 Change house keeping model from threded to checking timestamp on
#      each packet arrival
# 1.90 Added checking type of playback (video o audio). For video, status (playback or pause)
#      is checked and: resume or pause is sent and OSD notify. For audio only pause/resume is sent.
#      Varius debug cleanups
# 2.00 Added paused FE discovery durring call begin. If given FE is paused at call begin, call
#      end or cancel not resuming given FE.
# 2.01 Fixing missed threads->detach().
# 2.02 Fixing bug with wrong place telnet->close in telnet_and_osd_to host-
# 2.03 Changing myth_nofity messages to form required by 0.24 preliminary notifying mechanizm
# 2.04 Added caller num in loging messages
# 2.05 Fixing displaying mobile numbers as now they are without leading 0. Also some various tweaks
#      for script log output.
# 2.10 Adding telnum. blacklist. If caller or calling number matches eany number in 
#      blacklist - script will ingore this SIP message
# 2.21 Updated XML string sent to MythTV to supported by master     
# 2.22 Added OSD displayinfg timeout as MythTV now supports it. 

# Some SIP infos:
# INVITE: initiates sessions
#     session description included in message body offers
#     supported applications to request recepient: audio,
#     video, 
#     re-INVITEs used to update session state
# ACK: confirms session establishment
#     can only be used with INVITE
# CANCEL: cancels a pending INVITE
# BYE: terminates sessions
# REGISTER: binds a permanent address to current location
# OPTIONS: capability inquiry
#
#
# State machine:
# SIP msg->meeting->$callid   $curcallid  ->will do
# idle               " "     "first_call"
# 1st INVITE          X      "first_call" - pause and/or CID OSD; start housekeeping; curcallid=X
# N INVITE            X           X       - nothing
# other call INVITE   Y           X       - will only CID on OSD

# 1st BYE             X           X       - resume and/or notify "end" via OSD; kill housekeeping; curcallid="first_call"
# N BYE               X      "first_call" - nothing
# other call BYE      Y           X       - nothing
# orphan ACK          Y      "first_call" - nothing
#
# 1st CANCEL          X           X       - resume and/or notify "cancel" via OSD; kill housekeeping; curcallid="first_call"
# N CANCEL            X      "first_call" - nothing
# other call CANCEL   Y           X       - nothing
# orphan CANCEL       Y      "first_call" - nothing
#
# Housekeeping expiration after 3600sec will:
#                 $callid   $curcallid
#                   " "     "first_call"
#

use strict;
use warnings;
use IO::Socket;
use Net::Pcap;
use NetPacket::Ethernet qw(:strip);
use NetPacket::IP qw(:strip);
use NetPacket::TCP;
use NetPacket::UDP;
use Unicode::String qw(utf8 latin1 utf16);
use Net::Telnet;
use threads;
use threads::shared;

autoflush STDOUT 1;

######################################################################
#########   User Defined Variables                           #########
######################################################################
# Device on which SIP msgs will sniffed
my $dev='eth1';

# List of FE IPs for OSD notyfing and telneting for pause/resume
my $notifyaddr="127.0.0.1";

#my $your_phone_num = "poniszczuk002";
my $your_phone_num = "";

# List of blaclisted tel.numer. For those numbers script will 
# do nothing 
my $blacklist = "";

# If set to 0, script will not pause/resume on calls
my $pauseplayoncall = 1;

# Telnet command for paussing FEs when call starts
my $telnetpause = "key p";
# my $telnetpause="play speed pause";

# Telnet command for resuming FEs when call ends
my $telnetresume = "key p";
# my $telnetpause="play speed normal";

my $start_call_image = "images/mythnotify/phone-hangoff.png";
my $end_call_image = "images/mythnotify/phone-hangon.png";

# Set to 1 if You want to debufg SIP messages
my $debug = 0;

# Set it to housekeeping time. If after INVITE there is no
# BYE/CANCEL longer that this time - state machine will reset to IDLE
my $housekeep_tmo = 3600;

# How long OSD will show info about calls
my $start_call_osd_timeout = "15";
my $end_call_osd_timeout = "10";


#### Here are less interesting user defined variables ###############
my $debug2 = 0;
my $debugmsg = "";
my $quiet = 0;
my $filter_str = 'udp port 5060';
my $user = "root";
my $promisc = 0;
my $to_ms = 1000;

######################################################################
#########   End User Defined Variables--Modify nothing below #########
######################################################################


######################################################################
# global variables
######################################################################
my $pcap_t;
my $err;
my $count = -1;
### These shouldn't be changed (yet)
my $optimize=0;
my $netmask=0;
my $snaplen=50000;
my $callid=" ";
my $curcallid="first_call";
my $curack=0;
my $callernumber;
my $callingnumber;
my $callduration;
my $datestamp;
my $watchdog=-1;
my @pausedlist :shared;
######################################################################
# End child global variables
######################################################################

my($ver)='3.11';


&getOptions(@ARGV) || die "Could not get options\n";

sub telnet_and_notify_all_fe {

    my ($cmd1,$notify1,$caller1,$calling1,$date1,$ip_list) = @_;
    my @fe_list = ();

    @fe_list = split(/;/,$ip_list);

    for (@fe_list) {
        print "  Starting remote control thread for FE at $_ \n";
        my $th = threads->new(\&telnet_and_notify_fe,$cmd1,$notify1,$caller1,$calling1,$date1,$_);
        $th->detach();
    }

}

sub telnet_and_notify_fe {

    my ($cmd,$notify,$caller,$calling,$date,$ip) = @_;
    my $thr = threads->self->tid();

    if ($cmd eq "resume") {
        if ($notify eq "end") {
            print "  [Thread $thr]: Notify FE at $ip about ended call\n";
            if ($caller eq $your_phone_num) {
                &send_notify_to_host(
                    "TELEFON...",
                    "Zakończono połączenie",
                    "Do numeru:  ".$calling,
                    "Czas polaczenia: ".$date." sekund.",
                    $end_call_image,
                    "",
                    "",
                    $end_call_osd_timeout,
                    "",
                    $ip
               );
            }
            else {
                &send_notify_to_host(
                    "TELEFON...",
                    "Zakończono połączenie",
                    "Z numeru:  ".$caller,
                    "Czas polaczenia: ".$date." sekund.",
                    $end_call_image,
                    "",
                    "",
                    $end_call_osd_timeout,
                    "",
                    $ip
               );
            }
        }
        elsif ($notify eq "altend") {
            print "  [Thread $thr]: Notify FE at $ip about ended call\n";
            &send_notify_to_host(
                "TELEFON...",
                "Zakończono równoległe połączenie",
                "Z numeru:  ".$caller,
                "Do numeru: ".$caller,
                $end_call_image,
                "",
                "",
                $end_call_osd_timeout,
                "",
                $ip
            );
        }
    }

    if ($cmd eq "pause") {
        if ($notify eq "invite") {
            print "  [Thread $thr]: Notify FE at $ip about starting call\n";
            if ($caller eq $your_phone_num) {
                &send_notify_to_host(
                    "TELEFON...",
                    "",
                    "Wychodzące połączenie",
                    "Do numeru:  ".$calling,
                    $start_call_image,
                    "",
                    "",
                    $start_call_osd_timeout,
                    "",
                    $ip
                );
            }
            else {
                &send_notify_to_host(
                    "TELEFON...",
                    "",
                    "Przychodzące połączenie",
                    "Z numeru:  ".$caller,
                    $start_call_image,
                    "",
                    "",
                    $start_call_osd_timeout,
                    "",
                    $ip
                );
            }
        }
        elsif ($notify eq "altinvite") {
            print "  [Thread $thr]: Notify FE at $ip about starting call\n";
            &send_notify_to_host(
                "TELEFON...",
                "Rownoległe przychodzące połączenie",
                "Z numeru:  ".$caller,
                "Do numeru: ".$caller,
                $start_call_image,
                "",
                "",
                $start_call_osd_timeout,
                "",
                $ip
            );
        }
    }

    if ($notify eq "ongoing") {
        print "  [Thread $thr]: Notify FE at $ip about started call\n";
        if ($caller eq $your_phone_num) {
            &send_notify_to_host(
                "TELEFON...",
                "",
                "Rozpoczęto połączenie",
                "Z numeru:  ".$calling,
                $start_call_image,
                "",
                "",
                $end_call_osd_timeout,
                "",
                $ip
            );
        }
        else {
            &send_notify_to_host(
                "TELEFON...",
                "",
                "Rozpoczęto połączenie",
                "Do numeru:  ".$caller,
                $start_call_image,
                "",
                "",
                $end_call_osd_timeout,
                "",
                $ip
            );
        }
    }

    if ($cmd ne "") {
        my @lines = ();
        print "  [Thread $thr]: Trying remote control for $ip with command \"$cmd\" started\n";
        my $prompt = '/\# $/';
        my $telnet = new Net::Telnet(Timeout=>'10',
                               Errmode=>'return',
                               Port=>'6546',
                               Prompt=>$prompt);
        if ($telnet->open("$ip")) {
            $telnet->waitfor($prompt);
            @lines = $telnet->cmd('query location');
            my $location = join("\r",@lines);
            print "  [Thread $thr]: FE at $ip returns: $location";
            my $loc=$location;
            if ($loc =~ m/(Playback LiveTV|Playback Recorded|Playback Video|Playback DVD)/) {
                print "  [Thread $thr]: FE at $ip is in video playback cathegory. Checking state \n";
                my $loc=$location;
                if ($loc =~ m/pause/) {
                    print "  [Thread $thr]: FE at $ip is paused.\n";
                    if ($cmd eq "resume") {
                        print "  [Thread $thr]: Checking FE at $ip in paused list\n";
                        if (check_fe_paused_list($ip)) {
                            print "  [Thread $thr]: FE at $ip was paused when call starts, so no resume this FE\n";
                        }
                        else {
                            print "  [Thread $thr]: Resume Playback in FE at $ip\n";
                            print $telnet->cmd($telnetresume);
                        }
                    }
                    else {
                        print "  [Thread $thr]: Adding FE at $ip to paused list.\n";
                        add_fe_paused_list($ip);
                    }
                }
                else {
                    print "  [Thread $thr]: FE at $ip is playing.\n";
                    if ($cmd eq "pause") {
                        print "  [Thread $thr]: Pause Playback in FE at $ip\n";
                        print $telnet->cmd($telnetpause);
                    }
                }
            }
            else {
                my $loc=$location;
                if ($loc =~ m/(playmusic|mythstream)/) {
                    print "  [Thread $thr]: FE at $ip is in audio playback cathegory.\n";
                    if ($cmd eq "resume") {
                        print "  [Thread $thr]: Resume Playback in FE at $ip\n";
                        print $telnet->cmd($telnetresume);
                    }
                    if ($cmd eq "pause") {
                        print "  [Thread $thr]: Pause Playback in FE at $ip\n";
                        print $telnet->cmd($telnetpause);
                    }
                }
            }
            print $telnet->cmd('exit');
            $telnet->close;
            print "  [Thread $thr]: Closing Telent session\n";
        }
    }
    print "  [Thread $thr]: Job finished. Exiting\n";
}


sub send_notify_to_host {
    my ($title,$origin,$description,$extra,$image,$progress_text,$progress,$timeout,$style,$ip) = @_;
    my $msg = "";

    print ("OSD_notify:\n  title=\"$title\"\n  origin=\"$origin\"\n  description=\"$description\"\n  extra=\"$extra\"\n        image=\"$image\"\n  progress_txt=\"$progress_text\"\n  progress=$progress\n  style=\"$style\"\n  host=$ip\n") if ($debug);

    $msg ="<mythnotification version=\"1\">
         <image>$image</image>
         <text>$title</text>
         <origin>$origin</origin>
         <description>$description</description>
         <extra>$extra</extra>
         <progress_text>$progress_text</progress_text>
         <progress>$progress</progress>
         <timeout>$timeout</timeout>";
         if ($style) { $msg = $msg."
         <style>$style</style>" } $msg = $msg."
    </mythnotification>";

    print ("XML massage:\n".$msg."\n") if ($debug2);                                                                                                                                                     print ("Send data=\"$msg\"\n") if ($debug2);

    my $mythnotify_fh = IO::Socket::INET->new(PeerAddr=>$ip,Proto=>'udp',PeerPort=>6948);

    if ($mythnotify_fh) {
        print $mythnotify_fh $msg;
        $mythnotify_fh->close;
        print ("Notify via OSD to IP=$ip done\n") if ($debug);
    }
}

sub add_fe_paused_list {
    lock @pausedlist;
    if (check_fe_paused_list($_)) {
        print "  FE at $_ is already in paused FE list !!!\n";
    }
    else {
        @pausedlist = (@pausedlist,$_);
        #print "  Paused FE list is:@pausedlist\n";
    }
}


sub check_fe_paused_list {
    my($i, $found, $item)=0;
    $found=0;
    $i=0;
    lock @pausedlist;
    foreach $item (@pausedlist) {
        if ($item eq $_) {
            delete $pausedlist[$i];
            $found=1;
            print "  $_ found in paused FE list.Removing this FE from list.\n";
            last;
        }
    $i++;
    }
    return $found;
}


sub log_msg($) {
    my ($msg) = @_;
    print $msg . "\n";
}


sub convert_to_sec($) {
    my ($time) = @_;
    my $result = 0;
    if ($time =~ /(\d+):(\d+):(\d+)/) {
        my ($hr, $min, $sec) = ($1, $2, $3);
        $result = $hr * 3600 + $min * 60 + $sec;
    }
    $result;
}


sub adjnotation {
# take care about polish mobile and fixed numbers
    my $c = shift;
    if($c=~/^50/ or $c=~/^51/ or $c=~/^60/ or $c=~/^66/ or $c=~/^69/ or $c=~/^78/) {
        $c=~s/^(\d{3})(\d{3})(\d{3})$/$1-$2-$3/;
    }
    elsif ($c=~/^0/) {
        $c=~s/^(\d{3})(\d{3})(\d{2})(\d{2})$/$1-$2-$3-$4/;
    }
    else {
        $c=~s/^(\d{2})(\d{3})(\d{2})(\d{2})$/$1-$2-$3-$4/;
    }
    return $c;
}


sub filterascii {
    my $string = shift;
    $string = substr($string,0,16);
    $string =~ s/\W/_/g;
    return $string;
}

sub check_blacklist {
    my ($blist,$num) = @_;
    my @num_list = ();
    @num_list = split(/;/, $blist);
    print "  Checking isn't $num on blacklist...\n";
    for (@num_list) {
        print ("  Checking isn't $num equal to blacklisted num=$_ \n") if ($debug);;
        my $n=$num;
        if ($n=~/$_/) {
            print "  Number is matched with blackisted $_. Ignoring this SIP message...\n";
            return 1;
        }
    }
    return 0;
}

sub process_pkt {
  autoflush STDOUT 1;
  my($pktuser, $hdr, $pkt) = @_;

  if (!defined($hdr) or !defined($pkt)) {
    log_msg("Bad args passed to callback");
    log_msg("Bad user data"), if ($user ne "xyz");
    log_msg("Bad pkthdr"), if (!defined($hdr));
    log_msg("Bad pkt data"), if (!defined($pkt));
    log_msg("not ok");
    exit;
  }

  if ($watchdog != -1) {
    $callduration=time()-$watchdog;
    # print "  Checking watchdog. Time since first INVITE is: $callduration sec.\n";
    if (($watchdog + $housekeep_tmo) < time()) {
      print "  Watchdog: 3600sec since last INVITE and no BYE/CANCEL -> reseting variables and statemachine to IDLE.\n";
      $watchdog=-1;
      $callid=" ";
      $curcallid="first_call";
      $curack=0;
      @pausedlist=();
    }
  }

  #get datetimestamp of packet
  my ($sec, $min, $hour, $mday, $mon, $year)=localtime($hdr->{tv_sec});
  $year+=1900;
  $mon+=1;
  $datestamp="$hour:$min $mday\/$mon\/$year";
  my $debugtstamp="$hour:$min:$sec";

  #Strip Ethernet portion of packet off
  my $ip_obj=NetPacket::IP->decode(eth_strip($pkt));
  my $proto=$ip_obj->{proto};
  my ($tcp_obj, $udp_obj, $flags, $dataset);

  if($proto==17) {
    $udp_obj=NetPacket::UDP->decode(ip_strip(eth_strip($pkt)));
    $dataset=$udp_obj->{data};
  }

  print("-->Time: $debugtstamp <--\n$dataset\n") if ($debug2);
  my $invite=$dataset;

  if ($invite=~/INVITE sip:/) {
    $invite=$dataset;
    print "--> SIP INVITE msg detected. Time: $debugtstamp\n";
    #procesing invite message for getting caller phone number
    if ($invite=~/From:\s*"?(.*)"?\s*<sip:(.*)@/) {
      $callernumber = $2;
      if (check_blacklist($blacklist,$callernumber)) {return};
      $callernumber = filterascii($callernumber);
      $callernumber = adjnotation($callernumber);
      print "    Caller_Number:   $callernumber\n";
      #procesing invite message for getting calling phone number
      $invite=$dataset;
      $invite=~/To:\s*"?(.*)"?\s*<sip:(.*)@/;
      $callingnumber = $2;
      if (check_blacklist($blacklist,$callingnumber)) {return};
      # adjusting phone numers to polish notation
      $callingnumber = filterascii($callingnumber);
      $callingnumber = adjnotation($callingnumber);
      print "    Calling_Number:  $callingnumber\n";
      #procesing invite message for getting call-ID
      $invite=$dataset;
      $invite =~ m/Call-ID:\s*(.*)/;
      $callid = $1;
      print("    CallID:          $callid\n") if ($debug);
      # Comparing Call-ID in this INVITE msg with Call-ID from prevoius ones
      # If it is equal, silently dump it (as it is repeated INVITE).
      # If is diferent - it might be is first after silence or next try if
      # i.e. phone was busy. For first call, we will notify via
      # OSD and do telnet for pause. For next try - we will only notify via OSD.
      if ($callid ne $curcallid) {
        # It is not repeated INVITE. Checking is it first call or paralell call
        if ($curcallid eq "first_call") {
          # It is first call.
          print "First INVITE after idle. Pausing all FEs\n";
          print ("    CurrCallID:$callid\n    PrevCallID:$curcallid\n") if ($debug);
          $curcallid=$callid;
          # Telneting for pause (if enabled) or only notyfing via OSD to all
          # frontends about beginig call
          if ($pauseplayoncall) {
            telnet_and_notify_all_fe("pause","invite",$callernumber,$callingnumber,$datestamp,$notifyaddr);
          }
          else {
            telnet_and_notify_all_fe("","invite",$callernumber,$callingnumber,$datestamp,$notifyaddr);
          }
          # Launch housekeeping watchdog. Watchdog will reset after some time state machine to
          print "  Starting watchdog.\n";
          $watchdog=time();
        }
        else {
          # As $curcallid is diferent than "first_call" and $callid, it
          # is INVITE from paralel call
          print "INVITE from another call. Will only notify via OSD\n";
          print ("    CurrCallID:$callid\n    PrevCallID:$curcallid\n") if ($debug);
          telnet_and_notify_all_fe("","altinvite",$callernumber,$callingnumber,$datestamp,$notifyaddr);
        }
      }
      else {
        # As $curcallid is equal to $callid it
        # is repeated INVITE from first call.
        print "INVITE from thesame call (probably repeated INVITE or renegotiate params)\n";
        print ("    CurrCallID:$callid\n    PrevCallID:$curcallid\n") if ($debug);
      }
    }
  }
  if ($invite=~/BYE sip:/) {
    print "--> SIP BYE msg detected. Time: $debugtstamp\n";
    $invite=$dataset;
    $invite =~ m/Call-ID:\s*(.*)/;
    $callid = $1;
    # Checking is this first BYE for first call, repeated BYE for first call or
    # BYE for paralel call. If it is first BYE for first call - resume playback.
    # If it is repeated BYE for first call or BYE for paralell call - dump it
    if ($callid eq $curcallid) {
      # This is first BYE for first call.
      # Reseting $curcallid variable will ensure that repated BYE for first call
      # will not pause FEs again
      print "First BYE for first INVITE\n";
      print ("    CurrCallID:$callid\n    PrevCallID:$curcallid\n") if ($debug);
      $curcallid="first_call";
      $curack=0;
      # Telneting for resume (if enabled) or only notyfing via OSD to all
      # frontends about ending call
      if ($pauseplayoncall) {
        telnet_and_notify_all_fe("resume","end",$callernumber,$callingnumber,$callduration,$notifyaddr);
      }
      else {
        telnet_and_notify_all_fe("","end",$callernumber,$callingnumber,$callduration,$notifyaddr);
      }
      # Kiling house_keeping thread as call was sucessfuly ended
      print "  Stoping watchdog as session is successfuly ended\n";
      $watchdog=-1;
    }
    else {
      # As $curcallid is diferent than $callid it
      # is BYE from paralell call or repeated BYE from first call.
      print "Repeated BYE for first INVITE or BYE from other call.\n";
      print ("    CurrCallID:$callid\n    PrevCallID:$curcallid\n") if ($debug);
      telnet_and_notify_all_fe("","altend",$callernumber,$callingnumber,$datestamp,$notifyaddr);
    }
  }
  if ($invite=~/CANCEL sip:/) {
    print "--> SIP CANCEL msg detected. Time: $debugtstamp\n";
    $invite=$dataset;
    $invite =~ m/Call-ID:\s*(.*)/;
    $callid = $1;
    # Checking is this CANCEL for curr call. If it is not for first call - dump it
    if ($callid eq $curcallid) {
      # This is first CANCEL for first call.
      # Reseting $curcallid variable will ensure that repated BYE for first call
      # will not pause FEs again
      print "CANCEL for first INVITE.\n";
      print ("    CurrCallID:$callid\n    PrevCallID:$curcallid\n") if ($debug);
      $curcallid="first_call";
      $curack=0;
      # Telneting for resume (if enabled) or only notyfing via OSD to all
      # frontends about ending call
      if ($pauseplayoncall) {
        telnet_and_notify_all_fe("resume","cancel",$callernumber,$callingnumber,$datestamp,$notifyaddr);
      }
      else {
        telnet_and_notify_all_fe("","cancel",$callernumber,$callingnumber,$datestamp,$notifyaddr);
      }
      # Kiling house_keeping thread as call was sucessfuly ended
      print "  Stoping watchdog as session was canceled\n";
      $watchdog=-1;
    }
    else {
      # As $curcallid is diferent than $callid it
      # is CANCEL from paralell call or repeated CANCEL from first call.
      print "Repeated CANCEL for first INVITE or CANCEL from other call.\n";
      print ("    CurrCallID:$callid\n    PrevCallID:$curcallid\n") if ($debug);
      telnet_and_notify_all_fe("","altcancel",$callernumber,$callingnumber,$datestamp,$notifyaddr);
    }
  }
  if ($invite=~/ACK sip:/) {
    print "--> SIP ACK msg detected. Time: $debugtstamp\n";
    $invite=$dataset;
    $invite =~ m/Call-ID:\s*(.*)/;
    $callid = $1;
    # Checking is this ACK for curr call. If it is not for first call - dump it
    if ($callid eq $curcallid) {
      # This is first ACK for first call.
      # Reseting $curcallid variable will ensure that repated BYE for first call
      # will not pause FEs again
      print "OK for first INVITE.\n";
      print ("    CurrCallID:$callid\n    PrevCallID:$curcallid\n") if ($debug);
      if (! $curack) {
#        telnet_and_notify_all_fe("","ongoing",$callernumber,$callingnumber,$datestamp,$notifyaddr);
        $curack=1;
      }
    }
  }
  return;
}


sub getOptions {
  my(@ARGV)=@_;
  my $arg;
  if(scalar(@ARGV) > 0 && $ARGV[0]=~/--config=(.*)/){
    my $configfile=$1;
    open(CONFIG,"$configfile") || log_msg("Error opening config file, using defaults instead.");
    while(<CONFIG>){
      $arg=$_;
      if($arg!~/^\#/){
        $your_phone_num = $1         if ($arg=~/your_phone=(.*)/);
        $dev = $1                    if ($arg=~/device=(.*)/);
        $filter_str = $1             if ($arg=~/filter=(.*)/);
        $promisc = 1                 if ($arg=~/promisc=1/);
        $notifyaddr = $1             if ($arg=~/hosts_to_notify=(.*)/);
        $blacklist = $1              if ($arg=~/incomming_blacklist=(.*)/);
        $start_call_osd_timeout = $1 if ($arg=~/startosdduration=(.*)/);
        $end_call_osd_timeout = $1   if ($arg=~/endosdduration=(.*)/);
        $pauseplayoncall = $1        if ($arg=~/pause_on_calls=(.*)/);
        $telnetpause = $1            if ($arg=~/pause_cmd=(.*)/);
        $telnetresume = $1           if ($arg=~/resume_cmd=(.*)/);
        $to_ms = $1                  if ($arg=~/timeout=(.*)/);
        $quiet = 1                   if ($arg=~/quiet=1/);
        $debug = $1                  if ($arg=~/debug=(.*)/);
      }
    }
    close(CONFIG);
  }
  else {
    foreach $arg (@ARGV){
      $your_phone_num = $1         if ($arg=~/-num=(.*)/);
      $dev = $1                    if ($arg=~/-dev=(.*)/);
      $filter_str = $1             if ($arg=~/-filter=(.*)/);
      $promisc = $1                if ($arg=~/-promiscuous/);
      $notifyaddr = $1             if ($arg=~/-iplist=(.*)/);
      $blacklist = $1              if ($arg=~/-blacklist=(.*)/);
      $to_ms = $1                  if ($arg=~/-devicetimeout=(.*)/);
      $quiet = 1                   if ($arg=~/--quiet/);
      $pauseplayoncall = $1        if ($arg=~/-pauseoncalls/);
      $start_call_osd_timeout = $1 if ($arg=~/-startosdduration/);
      $end_call_osd_timeout = $1   if ($arg=~/-endosdduration/);
      if($arg=~/--h/ or $arg=~/-h/){
        print "**************\nSIP Call Notifier v$ver\n**************\n";
        print "SIP Call Notifier by James Armstrong,Kevin Venkiteswaran\n";
        print "                     Larry Silverman & Piotr Oniszczuk\n";
        print "\n###########\nTo use:\n";
        print "\t-num=<number>                  Specify your phone number\n";
        print "\t-dev=<dev>                     Specify the device from which packets are captured\n";
        print "\t-filter='filter'               String to filter on enclosed in single quotes\n";
        print "\t                               (DEFAULT: 'udp and port 5060')\n";
        print "\t-iplist=<IP>                   IP address list to which mythnotify messages are sent.\n";
        print "\t-blacklist=<blacklist>         IP address list to which mythnotify messages are sent.\n";
        print "\t-startosdduration>=integer     Duration of OSD message when call begins.\n";
        print "\t-endosdduration>=integer       Duration of OSD message when call ends.\n";
        print "\t-pauseoncalls>=0|1             Use telnet for pause/resume playback on calls.\n";
        print "\t-promiscuous=0|1               Place the device into promiscuous mode\n";
        print "\t-devicetimeout=integer         Read timeout in ms\n";
        print "\t--quiet                        Do not print anything but errors to STDOUT\n";
        print "\nDefaults:\n";
        print "\t-d=eth1\n\t-f='udp and port 5060'\n\t-p\n\t-t\n\t-to=1000\n";
        exit;
      }
    }
  }
  return 1;
}


print "\nSIP Call Notifier v$ver\n\n";
print "Running with following parameters:\n";
print "\tYour phone number:    $your_phone_num\n";
print "\tDevice to sniff SIP:  $dev\n";
print "\tHosts to notify:      $notifyaddr\n";
print "\tIncomming blacklst:   $blacklist\n";
print "\tOSD dur.for beg.call: $start_call_osd_timeout\n";
print "\tOSD dur.for end.call: $end_call_osd_timeout\n";
print "\tDevice timeout:       $to_ms\n";
print "\tRun quitet:           $quiet\n";
print "\tPause FEs on calls:   $pauseplayoncall\n";
print "\tFilter string:        $filter_str\n";
print "\tPromiscous mode:      $promisc\n";

log_msg("\nBeginning Sniff...\n");
$pcap_t=Net::Pcap::open_live($dev, $snaplen, $promisc, $to_ms, \$err) || die "Error opening pcap: $err\n"; #start sniffing
my $filter_t;
my $result=Net::Pcap::compile($pcap_t, \$filter_t, $filter_str,$optimize,$netmask); #compile filter_str
Net::Pcap::setfilter($pcap_t, $filter_t); #apply filter
Net::Pcap::loop($pcap_t, $count, \&process_pkt,"xyz"); #start to process the packets that are received
