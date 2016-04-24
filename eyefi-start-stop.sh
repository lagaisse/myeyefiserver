#!/bin/sh
#
# Startup script for eyefiserver.py
#
# Stop myself if running
PIDFILE=/XXXXXXXXXX/myeyefiserver/eyefiserver.pid
DSTPATH=/XXXXXXXXXX/myeyefiserver
PYTHONPATH=/bin

#
start() {
nohup ${PYTHONPATH}/python ${DSTPATH}/eyefiserver.py --conf ${DSTPATH}/eyefiserver.conf --log ${DSTPATH}/eyefiserver.log &
 # write pidfile
 echo $! > $PIDFILE
 echo "EyeFiServer started"
}
#
stop() {
 [ -f ${PIDFILE} ] && kill `cat ${PIDFILE}`
 # remove pidfile
 rm -f $PIDFILE 
 echo "EyeFiServer stopped"
}
#
case "$1" in
       start)
               start
       ;;
       stop)
               stop
       ;;
       restart)
               stop
               sleep 1
               start
       ;;
       *)
               echo "Usage: $0 (start|stop|restart)"
               exit 1
       ;;
esac
# End