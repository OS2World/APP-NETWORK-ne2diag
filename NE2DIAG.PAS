program ne2diag;

{$G+}
{$I-}
{$R-}
{$S-}

{$M 8192,0,655350}

uses newdelay, dos, crt;


{

0.02
fixed overflow bug
fixed buffering bugs
fixed bugs sending & receiving packets > 256 bytes

0.03
porting isr & critical code to assembly and optimising.. now buffer won't
overflow on lantastic 'startnet.bat' on 486SX-33. Promising!

0.04
added and io & irq select on commandline
increased rx packet buffer size slightly
buffer overflows still happening with heavy net raffic ie xcopy etc.

0.05
Added boundary pointer update after each packet rcvd. Speed increases LOTS
as a result. NS datasheet is WRONG; the boundary pointer does not auto-move
after one reads a packet!!

Program is now able to run on 486SX-25 with xcopy from win95 to NT4 server
without buffer overflows. First public release.


0.06

Found above statement in version 0.05 not quite true :-). Found more docs on
ne2000 cards; adjusted memory buffer layout; from 6.5k to 14.5k.. should be
MUCH better on slower PC's now.


}




const
  version	: string[5] = '0.06á';


  ioport	: word = $340;		{ Card I/O Port }
  irq		: byte = 9;


  txpktsize	: word = 1500;		{ 2k max!! }
  imr		: byte = $f;		{ Interupt mask register value }
  datawin	: word = (12*31)-1;		{ size of data window }


var
  eeprom	: array [0..$1f] of byte;
  sendbuffer	: array [0..2047] of byte;

  buffer	: array [0..2047] of byte;



  maclist	: array[1..49] of array[1..17] of byte;




  jabber,
  heart,
  fifoover,
  fifounder,
  txok,
  rxok,
  txbad,
  rxbad,
  coll,
  carrier,
  crcerrs,
  frame,
  flow		: longint;


  ch		: char;

  count,
  buff,
  nextpkt,
  j,
  k,
  i,
  hvl,
  picport	: word;

  rsr,
  btemp,
  bv,
  v,
  firstdisp,
  pichi,
  piclo,
  picval,
  int		: byte;

  disp,
  rxupdate,
  showbuff,
  sending	: boolean;

  oldint2	: pointer;



  par,
  cod		: integer;




  xtemp		: string[8];




function cvtb(b:byte) : byte;
begin
  if b>9 then cvtb:=b+ord('A')-10 else cvtb:=b+ord('0');
end;

function wrhex(byt:byte) : string;
begin
  wrhex:=chr(cvtb((byt and $f0) shr 4))+chr(cvtb(byt and $0f));
end;





procedure nictopc(page:word;buffwhere:word); assembler;
  asm
    mov dx,ioport
    add dx,8

    mov ax,page
    out dx,ax
    add dx,2
    mov ax,256
    out dx,ax
    sub dx,$a
    mov al,0ah
    out dx,al

    mov cx,128
    add dx,$10
    mov di,offset buffer
    mov bx,buffwhere
    add di,bx

    mov ax,ds
    mov es,ax

    rep insw

    sub dx,9
    mov al,$40
    out dx,al
end;



procedure pctonic(page,fromwhere:word); assembler;
  asm
    mov dx,ioport
    add dx,8

    mov ax,page
    out dx,ax
    add dx,2
    mov ax,256
    out dx,ax
    sub dx,$a
    mov al,012h
    out dx,al

    mov cx,128
    add dx,$10
    mov si,offset sendbuffer
    mov bx,fromwhere
    add si,bx

    rep outsw

    sub dx,9
    mov al,$40
    out dx,al
end;



{$F+}
procedure isr; interrupt;
begin
  asm
    mov ah,picval			{ Disable IRQ }
    not ah
    mov dx,picport
    in al,dx
    or al,ah
    out dx,al

    mov disp,true			{ tell main box to redraw }
  end;

  bv:=port[ioport+7];			{ why was the IRQ triggered ? }

{ RXerr }
  if bv and 4=4 then
  begin
    port[ioport+7]:=4;
    inc(rxbad);
    rsr:=port[ioport+$c];
    if (rsr and 2)=2 then inc(crcerrs);
    if (rsr and 4)=4 then inc(frame);
    if (rsr and 8)=8 then inc(fifoover);
    if (rsr and $80)=$80 then inc(jabber);
  end;


{ Overflow }
  if bv and $10=$10 then
  begin
    inc(flow);
    port[ioport]:=$21;			{ stop }
    delay(2);
    port[ioport+$a]:=0;
    port[ioport+$b]:=0;
    port[ioport+$d]:=2;
    port[ioport]:=$22;
    nictopc(nextpkt,0);
    nextpkt:=buffer[1] shl 8;
    btemp:=buffer[1]-1;
    if btemp<$40 then btemp:=$79-1;
    port[ioport+3]:=btemp;
    port[ioport+7]:=$10;
    port[ioport+$d]:=0;
  end;

{ TXOK }
  if bv and 2=2 then
  begin
    port[ioport+7]:=2;			{ clear received bit }
    inc(txok);
    rsr:=port[ioport+4];
    if rsr and 4=4 then coll:=coll+longint(port[ioport+5]);
    if rsr and $10=$10 then inc(carrier);
    if rsr and $80=$80 then inc(coll);
  end;

{ TXERR }
  if bv and 8=8 then
  begin
    port[ioport+7]:=8;
    inc(txbad);
    rsr:=port[ioport+4];
    if rsr and 8=8 then coll:=coll+16;
    if rsr and 4=4 then coll:=coll+longint(port[ioport+5]);
    if rsr and $80=$80 then inc(coll);
    if rsr and $10=$10 then inc(carrier);
    if rsr and $40=$40 then inc(heart);
    if rsr and $20=$20 then inc(fifounder);
  end;

{ RXOK }
  if bv and 1=1 then			{ RX ok }
  begin
    port[ioport+7]:=1;			{ clear received bit }
    buff:=0;
    inc(rxok);
    nictopc(nextpkt,0);

    btemp:=port[ioport+3];		{ update boundary; free buffer space }
    inc(btemp);
    if btemp>$78 then btemp:=$40;
    port[ioport+3]:=btemp;


    count:=256;
    while count<word(buffer[3] shl 8+buffer[2]) do
    begin
      buff:=buff+256;
      nextpkt:=nextpkt+$0100;
      if nextpkt>$7800 then nextpkt:=$4000;
      nictopc(nextpkt,buff);
      count:=count+256;


    btemp:=port[ioport+3];		{ update boundary; free buffer space }
    inc(btemp);
    if btemp>$78 then btemp:=$40;
    port[ioport+3]:=btemp;


    end;
    nextpkt:=buffer[1] shl 8;
    btemp:=buffer[1]-1;
    if btemp<$40 then btemp:=$78;
    port[ioport+3]:=btemp;		{ move boundary pointer }

    asm					{ process maclist }
      mov ax,ds
      mov es,ax
      mov di,offset maclist
      mov si,offset buffer

      mov ax,word ptr [si+2]		{ insert new val to maclist }
      rol ax,8
      mov [di+(17*48)+14],ax
      mov al,$ff
      mov [di+(17*48)+16],al

      mov cx,14/2
      add si,4
      add di,17*48
      rep movsw

      mov si,offset maclist		{ scroll maclist }
      mov di,si
      add si,17
      mov cx,(48*17)/4
      db $66;rep movsw

      mov rxupdate,true
    end;
  end;




{ Common exit code }

  asm
    mov dx,ioport			{ Card IRQ off }
    add dx,$f
    xor al,al
    out dx,al

    mov dx,picport			{ PIC IRQ on }
    mov al,picval
    out dx,al

    mov al,$20				{ ACK card IRQ }

    cmp dl,$a1
    jne @sk

    out $a0,al				{ 16-bit irq's only }

  @sk:
    out $20,al

    mov dx,ioport			{ Card IRQ on }
    add dx,$f
    mov al,imr
    out dx,al
  end;
end;
{$f-}



procedure mactree;
begin
  gotoxy(40,1);
  write('---To MAC--- --From MAC-- --Type--- Leng');
  for i:=firstdisp to 49 do
  begin
    gotoxy(40,i);
    if maclist[i][17]=$ff then
    begin
      write(wrhex(maclist[i][1]),wrhex(maclist[i][2]));
      write(wrhex(maclist[i][3]),wrhex(maclist[i][4]));
      write(wrhex(maclist[i][5]),wrhex(maclist[i][2]),' ');
      write(wrhex(maclist[i][7]),wrhex(maclist[i][8]));
      write(wrhex(maclist[i][9]),wrhex(maclist[i][10]));
      write(wrhex(maclist[i][11]),wrhex(maclist[i][12]),' ');


      case word(maclist[i][13] shl 8 + maclist[i][14]) of
        $0060 : write('Loopback  ');
        $0200 : write('Echo      ');
        $0400 : write('Xerox PUP ');
        $0600 : write('NS IDP    ');
        $0800 : write('IP        ');
        $0801 : write('X.75      ');
        $0802 : write('NBS       ');
        $0803 : write('ECMA      ');
        $0804 : write('CHAOSNet  ');
        $0805 : write('X.25      ');
        $0806 : write('ARP       ');
        $0888..$088a : write('Xyplex    ');
        $6010..$6014 : write('3Com ??   ');
        $81d6..$81d7 : write('Lantastic ');
        $8035 : write('RARP      ');
        $8037 : write('IPX (new) ');
	$8137..$8138 : write('IPX (old) ');
        $809b : write('EtherTalk ');
        $814C : write('SNMP      ');
        $86DD : write('IPv6      ');
        $8191 : write('NetBEUI   ');
        $9000 : write('Loopback  ');
        else write(wrhex(maclist[i][13]),wrhex(maclist[i][14]),'(???) ');
      end;
      write(wrhex(maclist[i][15]),wrhex(maclist[i][16]));
    end else writeln;
  end;
end;

function hextodec(c:char) : byte;
begin
  case upcase(c) of
    '0' : hextodec:=0;
    '1' : hextodec:=1;
    '2' : hextodec:=2;
    '3' : hextodec:=3;
    '4' : hextodec:=4;
    '5' : hextodec:=5;
    '6' : hextodec:=6;
    '7' : hextodec:=7;
    '8' : hextodec:=8;
    '9' : hextodec:=9;
    'A' : hextodec:=10;
    'B' : hextodec:=11;
    'C' : hextodec:=12;
    'D' : hextodec:=13;
    'E' : hextodec:=14;
    'F' : hextodec:=15;
  end;
end;



begin
  textmode(co80+font8x8);
  clrscr;
  sending:=false;
  showbuff:=true;
  firstdisp:=2;
  nextpkt:=$4100;
  rxupdate:=false;

{ Receive Packet buffer  = $40 - $79 = 16*256b = 14.5k }
{ transmit packet buffer = $7a - $7f = 16*256b = 1.5k }




{ Decode commandline }
  if paramcount>0 then
  begin
    ioport:=0;
    j:=1;
    for i:=length(paramstr(1)) downto 1 do
    begin
      xtemp:=copy(paramstr(1),i,1);
      ioport:=ioport+(hextodec(xtemp[1])*j);
      j:=j*$10;
    end;
  end;

  if paramcount=2 then
  begin
    val(paramstr(2),par,cod);
    irq:=lo(par);
  end;



{ Resolve IRQ stuf }
  if irq=2 then irq:=9;

  piclo:=port[$21];
  pichi:=port[$a1];


  if irq<8 then
  begin
    int:=8+irq;
    picport:=$21;
    case irq of
      3 : picval:=piclo and $f7;
      4 : picval:=piclo and $ef;
      5 : picval:=piclo and $df;
      7 : picval:=piclo and $7f;
    end;
  end else
  begin
    int:=$70+(irq-8);
    picport:=$a1;
    case irq of
      09 : picval:=pichi and $fd;
      10 : picval:=pichi and $fb;
      11 : picval:=pichi and $f7;
      12 : picval:=pichi and $ef;
      15 : picval:=pichi and $7f;
    end;
  end;


{ setup interrupt handler }
  getintvec(int,oldint2);
  setintvec(int,addr(isr));




{ load send buffer with raw data and destination address }
  for i:=0 to txpktsize-1 do sendbuffer[i]:=lo(i);
  sendbuffer[0]:=$ff;
  sendbuffer[1]:=$ff;
  sendbuffer[2]:=$ff;
  sendbuffer[3]:=$ff;
  sendbuffer[4]:=$ff;
  sendbuffer[5]:=$ff;


{ initialise card }
  v:=port[ioport+$1f];
  delay(10);
  port[ioport+$1f]:=v;
  delay(10);

  port[ioport]:=$21;			{ nic page 0, stop }
  port[ioport+$e]:=$59;			{ dataconfiguration }
  port[ioport+$a]:=0;			{ remote byte count }
  port[ioport+$b]:=0;
  port[ioport+$c]:=$1c;			{ receiveconfiguration }
  port[ioport+4]:=$7a;			{ tx page }
  port[ioport+$d]:=2;			{ tx configuration }

  port[ioport+1]:=$40;			{ rx page start }
  port[ioport+3]:=$40;			{ rx boundary }
  port[ioport+2]:=$79;			{ rx page stop }
  port[ioport]:=$61;			{ nic page 1, stop }
  port[ioport+7]:=$41;			{ rx current page }

  port[ioport]:=$21;			{ nic page 0, stop }
  port[ioport+7]:=$ff;			{ interruptstatus }
  port[ioport+$f]:=imr;			{ interruptmask }
  port[ioport+$d]:=0;			{ tx configuration }

{ Enable multicast reception }
  port[ioport]:=$61;			{ page 1 }
  port[ioport+8]:=$ff;
  port[ioport+$9]:=$ff;
  port[ioport+$a]:=$ff;
  port[ioport+$b]:=$ff;
  port[ioport+$c]:=$ff;
  port[ioport+$d]:=$ff;
  port[ioport+$e]:=$ff;
  port[ioport+$f]:=$ff;
  port[ioport]:=$21;			{ page 0 }


{ display NIC info }
  writeln('NE2000 at I/O ',wrhex(hi(ioport)),wrhex(lo(ioport)),'h, IRQ ',irq);
  write('EEPROM address ');
  nictopc(0,0);
  for i:=0 to $1f do eeprom[i]:=buffer[i];


{ Load our buffer }
  sendbuffer[6]:=eeprom[0];
  sendbuffer[7]:=eeprom[2];
  sendbuffer[8]:=eeprom[4];
  sendbuffer[9]:=eeprom[6];
  sendbuffer[$a]:=eeprom[8];
  sendbuffer[$b]:=eeprom[$a];

  j:=0;
  repeat
    write(wrhex(eeprom[j]));
    inc(j,2);
  until j>$0a;
  writeln;

  port[picport]:=picval;		{ IRQ on }
  port[ioport]:=$22;			{ Start! }






  repeat
{ Update stats only when required..faster! }
    if disp then
    begin
      gotoxy(1,5);
      writeln('Tx Total OK        : ',txok);
      writeln('Rx Total OK        : ',rxok);
      writeln('Tx Total Errors    : ',txbad);
      writeln('Rx Total Errors    : ',rxbad);
      writeln('Tx Collisions      : ',coll);
      writeln('Tx Carrier Lost    : ',carrier);
      writeln('Rx Buffer Overflow : ',flow);
      writeln('Rx CRC Error       : ',crcerrs);
      writeln('Rx Frame Error     : ',frame);
      writeln('Tx FIFO Underflow  : ',fifounder);
      writeln('Rx FIFO Overrun    : ',fifoover);
      writeln('Tx Heartbeat       : ',heart);
      writeln('Rx Defer (Jabber)  : ',jabber);

      mactree;

      if showbuff and rxupdate then
      begin
        gotoxy(1,19);
        hvl:=word(buffer[3]*256+buffer[2])-1;
        if hvl>datawin then hvl:=datawin;
        for i:=0 to hvl do
        begin
          write(wrhex(buffer[i]),' ');
          if i>0 then if (i+1) mod 12=0 then writeln;
        end;
        if hvl<datawin then for i:=hvl+1 to datawin do
        begin
          write('   ');
          if (i+1) mod 12=0 then writeln;
        end;
        rxupdate:=false;
      end;

      disp:=false;
    end;


{ Send }
    if sending and (port[ioport]<>$26) then		{ no tx if already TXing }
    begin
      asm
        cli
      end;
      for i:=0 to (txpktsize div 256) do pctonic($7a00+(i shl 8),i shl 8);
      asm
        mov dx,ioport
        add dx,4
        mov al,$7a
        out dx,al
        inc dx
        mov ax,txpktsize
        out dx,al
        inc dx
        mov al,ah
        out dx,al
        sub dx,6
        mov al,$26
        out dx,al

        sti
      end;
    end;



{ process keyboard }
    if keypressed then
    begin
      ch:=readkey;
      ch:=upcase(ch);
      if ch='S' then sending:=not sending;
      if ch='B' then
      begin
        showbuff:=not showbuff;
        if not showbuff then
        begin
          gotoxy(1,19);
          for i:=0 to datawin do
          begin
            write('   ');
            if i>0 then if (i+1) mod 12=0 then writeln;
          end;
        end;
      end;
      if ch='+' then if firstdisp>6 then
      begin
        dec(firstdisp,5);
        mactree;
      end;
      if ch='-' then if firstdisp<45 then
      begin
        inc(firstdisp,5);
        for i:=firstdisp-6 to firstdisp-1 do
        begin
          if i>1 then
	  begin
	    gotoxy(40,i);
            write('                                        ');
          end;
        end;
      end;
    end;

  until ch=#27;


{ reset interrupt handler, pic, screen, Stop NIC }

  port[ioport]:=$21;			{ offline }
  port[ioport+$f]:=0;			{ no int's }

  setintvec(int,oldint2);
  port[$a1]:=pichi;
  port[$21]:=piclo;
  gotoxy(1,50);
end.
