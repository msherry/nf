(defconstant +num-movies+ 17770)
(defconstant +num-users+ 480189)

(defvar *mid-sorted* nil)
(defvar *uid-sorted* nil)
(defvar *mid-index* nil)
(defvar *uid-index* nil)
(defvar *title-list* nil)
(defvar *uid-to-index-table* (make-hash-table :size +num-users+))

;; These use defparameter so we can clear them easily
(defparameter *user-features* (make-array 0 :adjustable T :fill-pointer 0))
(defparameter *movie-features* (make-array 0 :adjustable T :fill-pointer 0))


(defun create-mmap-file (filename)
  (with-open-file (map-file filename
			    :direction :output
			    :if-exists :supersede
			    :element-type '(unsigned-byte 64))
    ;; Header - have to fill up one word (4/8 bytes), regardless of element-type
    (write-byte sb-vm::simple-array-unsigned-byte-60-widetag map-file)
    ;; Array size placeholder - ditto on the 4/8 bytes
    (write-byte 8 map-file)
    (let ((files (directory (merge-pathnames #P"download/training_set/*.*")))
	  (stars-total 0)
	  (num-ratings 0))
      (dolist (file files)
	(with-open-file (stream file)
	  (let ((index (parse-integer (read-line stream) :junk-allowed t)))
	    (when (zerop (mod index 100)) (print file))
	    (let ((lines (loop for line = (read-line stream nil nil)
			       while line
			       collect line)))
	      (loop for line in lines
		    do (multiple-value-bind (uid end)
			   (parse-integer line :junk-allowed t)
			 (let* ((stars (parse-integer line
						      :start (1+ end)
						      :junk-allowed t))
				(data (ash (logior uid
						   (ash index 32)
						   (ash stars (+ 32 16)))
					   sb-vm:n-fixnum-tag-bits)))
			   (write-byte data map-file)
			   (incf stars-total stars)
			   (incf num-ratings))))))))
      (file-position map-file 1) ;go back to the array size placeholder

      ;; Little-endian is retarded
      (write-byte (ash num-ratings sb-vm:n-fixnum-tag-bits) map-file)
      (format t "~%Total stars: ~a~%Number of ratings: ~a~%Average rating: ~a"
	      stars-total num-ratings (float (/ stars-total num-ratings))))))

(defun load-mmap-file (filename variable)
  (with-open-file (file filename)
    (let* ((sap (sb-posix:mmap nil
                               (file-length file)
                               sb-posix:prot-read
                               sb-posix:map-private
                               (sb-impl::fd-stream-fd file)
                               0))
           (addr (logior (sb-sys:sap-int sap)
                         sb-vm:other-pointer-lowtag)))
      (print (list sap (sb-sys:sap-int sap)))
      (setf (symbol-value variable) (sb-kernel:make-lisp-obj addr))
      (values))))   ;So we don't return the entire vector - slow

(defun save-features ()
  (let ((*print-pretty* nil)
	(*print-array* T)
	(*print-length* nil)
	(*print-level* nil))
    (with-open-file (out "user-features.dat" 
		     :direction :output
		     :if-exists :supersede)
      (prin1 *user-features* out))
    (with-open-file (out "movie-features.dat"
		     :direction :output
		     :if-exists :supersede)
      (prin1 *movie-features* out)))
  (values))

(defun find-ratings-by-mid (mid)
  (declare (optimize (speed 3) (safety 0))
	   (fixnum mid))
  (let ((low (svref *mid-index* (1- mid)))
	(high (svref *mid-index* mid)))
    (declare (fixnum low) (fixnum high))
    ;(subseq (the (simple-array fixnum) *mid-sorted*) low high)))
    (make-array (- high low) :element-type '(unsigned-byte 60)
		:displaced-to *mid-sorted* :displaced-index-offset low)))

(defun num-ratings-by-mid (mid)
  (let ((low (svref *mid-index* (1- mid)))
	(high (svref *mid-index* mid)))
    (- high low)))

(defun find-ratings-by-uid (uid)
  (declare (optimize (speed 3) (safety 0))
	   (fixnum uid))
  (let ((indexed-uid (convert-uid-to-index uid)))
    (declare (fixnum indexed-uid))
    (let ((low (svref *uid-index* (1- indexed-uid)))
	  (high (svref *uid-index* indexed-uid)))
      (declare (fixnum low) (fixnum high))
      (subseq (the (simple-array fixnum) *uid-sorted*) low high))))

(defun num-ratings-by-uid (uid)
  (let ((low (svref *uid-index* (1- (convert-uid-to-index uid))))
	(high (svref *uid-index* (convert-uid-to-index uid))))
    (- high low)))

(declaim (inline find-rating-by-mid-and-uid))
(defun find-rating-by-mid-and-uid (mid uid)
  (declare (optimize (speed 3) (safety 0))
	   (fixnum mid uid))
  (fast-find uid (find-ratings-by-mid mid)))

(defun find-movie-title (mid)
  (svref *title-list* (1- mid)))

(defun create-uid-to-index-table ()
  "Create a mapping from real user id (~22 bits, with gaps) to a
  scaled-down version (no gaps, starting with 0)"
   (declare (optimize (speed 3) (safety 0))
 	   (type (simple-array fixnum) *uid-sorted*))
  (let ((index 0)
	(last -1))
    (declare (fixnum index last))
    (loop for i fixnum across *uid-sorted* do
	  (let ((uid (extract-uid i)))
	    (declare (fixnum uid))
	    (when (/= uid last)
	      (setf (gethash uid *uid-to-index-table*) index)
	      (incf index)
	      (setq last uid))))))

(declaim (inline convert-uid-to-index))
(defun convert-uid-to-index (uid)
  "Convert the full uid to the scaled-down version"
  (declare (optimize (speed 3) (safety 0))
	   (fixnum uid))
  (gethash uid *uid-to-index-table*))

(defun create-mid-index (mid-list)
  "Array index is movie id, array data is index of first rating of this movie in 
  (list of ratings sorted by movie id)"
   (declare (optimize (speed 3) (safety 0))
	    (type (simple-array fixnum) mid-list))
  (let ((index nil)
	(last -1))
    (declare (fixnum last))
    (loop for item fixnum across mid-list
	  for pos fixnum from 0
	  do
	  (let ((mid (extract-mid item)))
	    (declare (fixnum mid))
	    (when (/= mid last)
	      (push pos index)
	      (setq last mid)))
	  finally
	  (push (the fixnum (1+ pos)) index)) ;fencepost issue - this makes find-ratings-by-user simpler
    (map 'vector 'identity (nreverse index)))) ;reverse and vectorize index

(defun create-uid-index (uid-list)
  "Array index is scaled-down user id (no gaps), array data is index of first
  rating by this user in (list sorted by user id)"
   (declare (optimize (speed 3) (safety 0))
 	   (type (simple-array fixnum) uid-list))
  (let ((index nil)
	(last -1))
    (declare (fixnum last))
    (loop for item fixnum across uid-list
	  for pos fixnum from 0
	  do
	  (let ((uid (convert-uid-to-index (extract-uid item))))
	    (declare (fixnum uid))
	    (when (/= uid last)
	      (push pos index)
	      (setq last uid)))
	  finally
	  (push (the fixnum (1+ pos)) index))
    (map 'vector 'identity (nreverse index)))) ;reverse and vectorize index

(defun create-title-list ()
  ;; Array index is movie id, array data is title (plus other junk)
  (let ((movies nil))
    (with-open-file (s "download/movie_titles.txt"
		       :external-format :ISO-8859-1) ;necessary to handle words like "cafe" (with accent)
      (let ((lines (loop for line = (read-line s nil nil)
			 while line
			 collect line)))
	(loop for line in lines 
	      do
	      (push line movies))))
    (map 'vector 'identity (nreverse movies))))

(defmacro wait-text (text &body body)
  `(progn
    (format t ,text)
    ,@body
    (format t "done!~%")))

(defun load-all-files ()
  (load-mmap-file "mid-uid-sorted" '*mid-sorted*)
  (load-mmap-file "uid-mid-sorted" '*uid-sorted*)
  (format t "~%")
  (wait-text "Creating uid-to-index table... "
    (create-uid-to-index-table))
  (wait-text "Loading mid index... "
    (with-open-file (in "mid-index")
      (defparameter *mid-index* (read in))))
   (wait-text "Loading uid index... "
     (with-open-file (in "uid-index")
       (defparameter *uid-index* (read in))))
;;   (wait-text "Creating mid index... "
;;     (defparameter *mid-index* (create-mid-index *mid-sorted*)))
;;    (wait-text "Creating uid index... "
;;      (defparameter *uid-index* (create-uid-index *uid-sorted*)))
   (wait-text "Creating title list... "
     (defparameter *title-list* (create-title-list))))

(defun clear-all-features ()
  (defparameter *user-features* (make-array 0 :adjustable T :fill-pointer 0))
  (defparameter *movie-features* (make-array 0 :adjustable T :fill-pointer 0)))

(defun add-new-feature ()
  "Return value is the index of the feature we just added."
  ;1+ to avoid mid->index conversion - wastes first slot
  (let ((init-val (/ .1 (1+ (length *user-features*)))))
    (vector-push-extend (make-array +num-users+ :initial-element init-val) *user-features*)
    (vector-push-extend (make-array (1+ +num-movies+) :initial-element init-val) *movie-features*)))

(defun pop-last-feature ()
  "Remove the last feature added - usually used during testing."
  (vector-pop *user-features*)
  (vector-pop *movie-features*)
  (values))

(defun train-all-features (&key (max-feature 9) (epochs 25) (step 10) (show-rmse T))
  (gc :full t)
  (let ((rating-cache (make-array (length *uid-sorted*) :initial-element 0.0 :adjustable nil :fill-pointer nil)))
    (wait-text "Creating rating cache... "
      (create-rating-cache rating-cache))
    (loop for feature from (or (length *user-features*) 0) to max-feature do
	  (format t "Feature: ~a~%" feature)
	  (wait-text "Running garbage collection... "
	    (gc :full t))			;try to avoid thrashing
	  (add-new-feature)
	  (loop for epoch from 1 to (+ epochs (* feature step)) do
		(when (zerop (mod epochs 10))
		  (format t "Epoch: ~a~%" epoch))
		(train-feature feature rating-cache))
	  (wait-text "Updating rating cache... "
	    (update-rating-cache rating-cache feature))
	  (when show-rmse
	    (gc :full t)
	    (process-datafile "download/probe.txt" :nolimit T))
	  (format t "Most: ~%~A~%" (find-movies-by-feature feature :num 40 :fn '>))
	  (format t "Least: ~%~A~%" (find-movies-by-feature feature :num 40 :fn '<)))))

(defun train-feature (feature rating-cache)
  (declare (optimize (speed 3) (safety 0))
	   (fixnum feature)
	   (type (simple-array fixnum) *uid-sorted*)
	   (type (array simple-array) *user-features* *movie-features*))
  (let ((u-f (aref *user-features* feature))
	(m-f (aref *movie-features* feature))
	(last-uid -1) (uid-index -1))
    (declare (simple-array u-f m-f)
	     (fixnum last-uid uid-index))
    (loop for r fixnum across *uid-sorted*
	  for i fixnum from 0
	  do
	  (let ((uid (extract-uid r)))
	    (declare (fixnum uid))
	    (when (/= uid last-uid)
	      (setq last-uid uid
		    uid-index (convert-uid-to-index uid)))
	  (let* ((mid (extract-mid r))
		 (uv (svref u-f uid-index))
		 (mv (svref m-f mid))
		 (err (* .001 (- (the fixnum (extract-stars r))
				 (the single-float (caching-predict-user-rating uv mv rating-cache i))))))
	    (declare (fixnum mid)
		     (single-float uv mv err))
	  (incf (the single-float (svref u-f uid-index)) (the single-float (* err mv)))
	  (incf (the single-float (svref m-f mid)) (the single-float (* err uv))))))))

(defun update-rating-cache (cache feature)
  (declare (optimize (speed 3) (safety 0))
	   (simple-vector cache)
	   (type (simple-array fixnum) *uid-sorted*)
	   (type (array simple-array) *user-features* *movie-features*))
  (let ((u-f (aref *user-features* feature))
	(m-f (aref *movie-features* feature))
	(last-uid -1)
	(uid 0) (uid-index 0) (mid 0))
    (declare (fixnum last-uid uid uid-index mid))
    (loop for r fixnum across *uid-sorted*
	  for i fixnum from 0
	  do
	  (setq uid (extract-uid r))
	  (when (/= uid last-uid)
	    (setq last-uid uid
		  uid-index (convert-uid-to-index uid)))
	  (setq mid (extract-mid r))
	  (incf (the single-float (svref cache i))
		(the single-float (* (the single-float (svref u-f uid-index))
				     (the single-float (svref m-f mid))))))))

(defun create-rating-cache (cache)
  (declare (optimize (speed 3) (safety 0))
	   (simple-vector cache)
	   (type (simple-array fixnum) *uid-sorted*)
	   (type (array simple-array) *user-features* *movie-features*))
  (let ((last-uid -1) (uid-index -1))
    (declare (fixnum last-uid uid-index))
    (loop for r fixnum across *uid-sorted*
	  for i fixnum from 0
	  do
	  (let ((uid (extract-uid r)))
	    (declare (fixnum uid))
	    (when (/= uid last-uid)
	      (setq last-uid uid
		    uid-index (convert-uid-to-index uid)))
	    (let ((mid (extract-mid r)))
	      (declare (fixnum mid))
	      (setf (svref cache i)
		    (loop for u-f simple-vector across *user-features*
			  for m-f simple-vector across *movie-features*
			  sum
			  (* (the single-float (svref u-f uid-index))
			     (the single-float (svref m-f mid)))
			  into result single-float
			  finally
			  (return result))))))))

(defun caching-predict-user-rating (uv mv rating-cache rating-num)
  (declare (optimize (speed 3) (safety 0))
	   (single-float uv mv)
	   (simple-vector rating-cache))
  (let ((predicted (+ (the single-float (* uv mv))
		      (the single-float (svref rating-cache rating-num)))))
    (declare (single-float predicted))
    (cond ((> predicted 5.0) 5.0)
	  ((< predicted 1.0) 1.0)
	  (T predicted))))

(defun predict-user-rating (uid-index mid)
  (declare (optimize (speed 3) (safety 0))
	   (fixnum uid-index mid)
	   (type (array simple-array) *user-features* *movie-features*))
  (loop for u-f simple-vector across *user-features*
	for m-f simple-vector across *movie-features*
	sum
	(* (the single-float (svref u-f uid-index))
	   (the single-float (svref m-f mid)))
	into result single-float
	finally
	(return (cond ((> result 5.0) 5.0)
;; 		      ((and (< result 4.05)
;; 			    (> result 3.95)) 4.0)
;; 		      ((and (< result 3.05)
;; 			    (> result 2.95)) 3.0)
;; 		      ((and (< result 2.05)
;; 			    (> result 1.95)) 2.0)
		      ((< result 1.0) 1.0)
		      (T result)))))

(defun fast-find (item sequence &optional (start 0) (end (1- (length sequence))))
  (let* ((mid (truncate (/ (+ end start) 2)))
	 (rating (aref sequence mid))
	 (uid (extract-uid rating)))
  (cond ((< end start) nil)
	((> uid item) (fast-find item sequence start (1- mid)))
	((< uid item) (fast-find item sequence (1+ mid) end))
	(T rating))))

(defun process-datafile (datafile &key (count 100) (nolimit nil) (outfile "probe-output.txt"))
  (declare (optimize (speed 3) (safety 0))
	   (fixnum count))
  (unless *uid-sorted* (load-all-files))
  (let ((cur-mid 0)
	(total-error 0.0)
	(num-processed 0)
	(ratings-by-mid))
    (declare (fixnum cur-mid num-processed)
	     (single-float total-error))
    (with-open-file (s datafile)
      (with-open-file (out outfile
		       :direction :output
		       :if-exists :supersede)
	(loop for line = (read-line s nil nil)
	      while (and line
			 (or nolimit
			     (< num-processed count)))
	      do
	      (cond ((find #\: line :from-end T)
		     (setq cur-mid (parse-integer line :junk-allowed t))
		     (setq ratings-by-mid (find-ratings-by-mid cur-mid))
		     ;(format t "~a:~%" cur-mid)
		     (format out "~a:~%" cur-mid))
		    (T
		     (let* ((uid (parse-integer line :junk-allowed t))
			    (predicted (predict-user-rating (convert-uid-to-index uid) cur-mid))
			    (this-rating (fast-find uid ratings-by-mid))
			    (actual (if this-rating (extract-stars this-rating) 0)))
			    ;(actual 0))
		       (declare (single-float predicted)
				(fixnum actual))
		       (incf total-error (the single-float (expt (- predicted actual) 2)))
		       (incf num-processed)
		       ;(format t "~a~,7@t~a~,17@t~a~,15@t~a~,5@t~a~,15t~a~%" cur-mid uid predicted actual (sqrt (/ total-error num-processed)) num-processed)
		       (format out "~a~%" predicted))))))
      (let ((final-rmse (the single-float (sqrt (the single-float (/ total-error num-processed))))))
	(format t "RMSE: ~a~%" final-rmse)
	final-rmse))))

(defun find-movies-by-feature (feature &key (num 40) (fn #'>))
  (map 'vector #'(lambda(x) (find-movie-title (svref x 0)))
       (subseq (sort (loop for i from 1 to +num-movies+ collect
			   (vector i (svref (aref *movie-features* feature) i)))
		     fn
		     :key #'(lambda(x) (svref x 1)))
	       0 num)))

(defun average-movie-stars (mid)
  (float (/ (loop for r across (find-ratings-by-mid mid)
		  sum
		  (extract-stars r))
	    (num-ratings-by-mid mid))))

(declaim (inline extract-stars))
(defun extract-stars (packed)
  (declare (optimize (speed 3) (safety 0))
	   (fixnum packed))
  (ash packed -48))			;upper 16 bits

(declaim (inline extract-mid))
(defun extract-mid (packed)
  (declare (optimize (speed 3) (safety 0))
	   (fixnum packed))
  (logand (ash packed -32) 65535))	;bits 32-48

(declaim (inline extract-uid))
(defun extract-uid (packed)
  (declare (optimize (speed 3) (safety 0))
	   (fixnum packed))
  (logand packed 4294967295))		;lower 32 bits

(defun extract-all (packed)
  (vector (extract-uid packed) (extract-mid packed) (extract-stars packed)))


;; Unused
;; (defun non-caching-train-all-features (&key (max-feature 9) (epochs 25) (step 10))
;;   (loop for feature from (or (length *user-features*) 0) to max-feature do
;; 	(format t "Feature: ~a~%" feature)
;; 	(add-new-feature)
;; 	(loop for epoch from 1 to (+ epochs (* feature step)) do
;; 	      (format t "Epoch: ~a~%" epoch)
;; 	      (non-caching-train-feature feature)
;; 	      (when (zerop (mod epoch 10))
;; 		(process-datafile "download/probe.txt" :nolimit T)))
;; 	(format t "Most: ~%~A~%" (find-movies-by-feature feature :num 40 :fn '>))
;; 	(format t "Least: ~%~A~%" (find-movies-by-feature feature :num 40 :fn '<))))

;; (defun non-caching-train-feature (feature)
;;   (declare (optimize (speed 3) (safety 0))
;; 	   (fixnum feature)
;; 	   (type (simple-array fixnum) *uid-sorted*)
;; 	   (type (array simple-array) *user-features* *movie-features*))
;;   (let ((user-features (aref *user-features* feature))
;; 	(movie-features (aref *movie-features* feature))
;; 	(last-uid -1) (last-uid-index -1))
;;     (declare (simple-array user-features movie-features)
;; 	     (fixnum last-uid last-uid-index))
;;     (loop for r fixnum across *uid-sorted* do
;; 	  (let* ((uid (extract-uid r))
;; 		 (uid-index (cond ((= uid last-uid) last-uid-index)
;; 				      (T (setf last-uid uid)
;; 					 (setf last-uid-index (convert-uid-to-index uid))
;; 					 last-uid-index)))
;; 		 (mid (extract-mid r))
;; 		 (uv (svref user-features uid-index))
;; 		 (mv (svref movie-features mid))
;; 		 (err (* .001 (- (the fixnum (extract-stars r))
;; 				 (the single-float (predict-user-rating uid-index mid))))))
;; 	    (declare (single-float uv mv err)
;; 		     (fixnum uid uid-index mid))
;; 	    (incf (the single-float (svref user-features uid-index)) (the single-float (* err mv)))
;; 	    (incf (the single-float (svref movie-features mid)) (the single-float (* err uv)))))))

;; (defun consing-train-feature (feature rating-cache)
;;   (declare (optimize (speed 3) (safety 0))
;; 	   (fixnum feature)
;; 	   (type (simple-array fixnum) *uid-sorted*)
;; 	   (type (array simple-array) *user-features* *movie-features*))
;;   (let ((user-features (aref *user-features* feature))
;; 	(movie-features (aref *movie-features* feature))
;; 	(last-uid -1) (last-uid-index -1))
;;     (declare (simple-array user-features movie-features)
;; 	     (fixnum last-uid last-uid-index))
;;     (loop for r fixnum across *uid-sorted*
;; 	  for i fixnum from 0
;; 	  do
;; 	  (let* ((uid (extract-uid r))
;; 		 (uid-index (cond ((= uid last-uid) last-uid-index)
;; 				      (T (setf last-uid uid)
;; 					 (setf last-uid-index (convert-uid-to-index uid))
;; 					 last-uid-index)))
;; 		 (mid (extract-mid r))
;; 		 (uv (svref user-features uid-index))
;; 		 (mv (svref movie-features mid))
;; 		 (err (* .001 (- (the fixnum (extract-stars r))
;; 				 (the single-float (caching-predict-user-rating uv mv feature rating-cache i))))))
;; 	    (declare (single-float uv mv err)
;; 		     (fixnum uid uid-index mid))
;; 	    (incf (the single-float (svref user-features uid-index)) (the single-float (* err mv)))
;; 	    (incf (the single-float (svref movie-features mid)) (the single-float (* err uv)))))))

;; (defun non-cache-updating-train-all-features (&key (max-feature 9) (epochs 25) (step 10))
;;   (let ((rating-cache (make-array (length *uid-sorted*) :adjustable nil :fill-pointer nil)))
;;     (loop for feature from (or (length *user-features*) 0) to max-feature do
;; 	  (format t "Feature: ~a~%" feature)
;; 	  (wait-text "Running garbage collection... "
;; 	    (gc :full t))			;try to avoid thrashing
;; 	  (when (> feature 0) (create-rating-cache rating-cache))
;; 	  (add-new-feature)
;; 	  (loop for epoch from 1 to (+ epochs (* feature step)) do
;; 		(format t "Epoch: ~a~%" epoch)
;; 		(train-feature feature rating-cache))
;; 	  ;(process-datafile "download/probe.txt" :nolimit T)
;; 	  (format t "Most: ~%~A~%" (find-movies-by-feature feature :num 40 :fn '>))
;; 	  (format t "Least: ~%~A~%" (find-movies-by-feature feature :num 40 :fn '<)))))

