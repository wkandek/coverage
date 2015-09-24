coverage.pl calculates the scan coverage that a certain Option Profile provided in the last X days

It downloads the data from the Qualys API. Username, password, URLs etc are specified in coverage.conf

A typical run would be perl coverage.pl --verbose - which gives some info about the run on the display.
A logfile coverage.log has data for debugging purposes, especially if --debug is given on the command line

The --nodownload option is handy when the files are alreay on disc (i.e. ag.xml and sh.xml) and to do
some debugging, i.e. by changing the targets in sh.xml or the list of IPs in ag.xml.

Take a look at simple_ag.xml and simple_sh.xml for very short example files.
- test cases: 10.1.1.1-10.10.255.255 
  - 10.1.1.1
  - 10.10.255.255
  - 10.5.1.1
  - 10.1.1.1-10.10.255.255

In coverage.conf one specifies the AG, the SLA in days and the Option Profile that one is intersted in.

Useful commandline: rm coverage.log ; perl coverage.pl --nodownload --verbose --debug

Example: (works with the simple_ag and simple_sh files)

<pre><code>
&lt;COVERAGECONFIG&gt;
&lt;URL&gt;qualysapi.qualys.com&lt;/URL&gt;
&lt;USERNAME&gt;q_sp&lt;/USERNAME&gt;
&lt;PASSWORD&gt;xxx&lt;/PASSWORD&gt;
&lt;AGLIST&gt;
  &lt;AG scansla="3000" op="All Windows machines" &gt;Ops&lt;/AG&gt;
&lt;/AGLIST&gt;
&lt;/COVERAGECONFIG&gt;
</code></pre>
