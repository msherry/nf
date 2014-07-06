(defvar *num-movies* 17770)
(defvar *num-users* 480189)
(defvar *mid-sorted* nil)
(defvar *uid-sorted* nil)
(defvar *mid-index* nil)
(defvar *uid-index* nil)
(defvar *title-list* nil)
(defvar *uid-to-index-table* (make-hash-table))

(defparameter *num-of-correlations* 20)
(defparameter *max-sequence-length* 100)

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
      (values))))   ;So we don't return the entire list - slow

(defun find-ratings-by-mid (mid)
  (declare (optimize (speed 3) (safety 0))
	   (fixnum mid))
  (let ((low (svref *mid-index* (1- mid)))
	(high (svref *mid-index* mid)))
    (declare (fixnum low) (fixnum high))
    (subseq (the (simple-array fixnum) *mid-sorted*) low high)))

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

(defun nfind-ratings-by-uid (uid)
  (declare (optimize (speed 3) (safety 0))
	   (fixnum uid))
  (let ((indexed-uid (convert-uid-to-index uid)))
    (declare (fixnum indexed-uid))
    (let ((low (svref *uid-index* (1- indexed-uid)))
	  (high (svref *uid-index* indexed-uid)))
      (declare (fixnum low) (fixnum high))
      (vector low high))))

(defun num-ratings-by-uid (uid)
  (let ((low (svref *uid-index* (1- (convert-uid-to-index uid))))
	(high (svref *uid-index* (convert-uid-to-index uid))))
    (- high low)))

(defun find-rating-by-mid-and-uid (mid uid)
  (find uid (find-ratings-by-mid mid) :key 'extract-uid))

(defun find-users-who-rated (mid)
  (map 'vector 'extract-uid (find-ratings-by-mid mid)))

(defun find-movie-title (mid)
  (svref *title-list* (1- mid)))

(defun create-mid-index (mid-list)
  "Array index is movie id, array data is index of first rating of this movie in 
  (list of ratings sorted by movie id)"
  (let ((index nil)
	(last -1))
    (loop for item across mid-list
	  for pos from 0
	  do
	  (let ((mid (extract-mid item)))
	    (when (/= mid last)
	      (push pos index)
	      (setf last mid)))
	  finally
	  (push (1+ pos) index))	;fencepost issue - this makes find-ratings-by-user simpler
    (map 'vector 'identity (nreverse index)))) ;reverse and vectorize index

(defun create-uid-to-index-table ()
  "Create a mapping from real user id (~22 bits, with gaps) to a
  scaled-down version (no gaps, starting with 1)"
  (let ((index 1)
	(last -1))
    (loop for i across *uid-sorted* do
	  (let ((uid (extract-uid i)))
	    (when (/= uid last)
	      (setf (gethash uid *uid-to-index-table*) index)
	      (incf index)
	      (setf last uid))))))

(declaim (inline convert-uid-to-index))
(defun convert-uid-to-index (uid)
  "Convert the full uid to the scaled-down version"
  (declare (optimize (speed 3) (safety 0))
	   (fixnum uid))
  (gethash uid *uid-to-index-table*))

(defun create-uid-index (uid-list)
  "Array index is scaled-down user id (no gaps), array data is index of first 
  rating by this user in (list sorted by user id)"
  (let ((index nil)
	(last -1))
    (loop for item across uid-list
	  for pos from 0
	  do
	  (let ((uid (convert-uid-to-index (extract-uid item))))
	    (when (/= uid last)
	      (push pos index)
	      (setf last uid)))
	  finally
	  (push (1+ pos) index))
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
  (load-mmap-file "mid-sorted" '*mid-sorted*)
  (load-mmap-file "uid-mid-sorted" '*uid-sorted*)
  (format t "~%")
  (wait-text "Creating uid-to-index table... "
    (create-uid-to-index-table))
  (wait-text "Creating mid index... "
    (defparameter *mid-index* (create-mid-index *mid-sorted*)))
  (wait-text "Creating uid index... "
    (defparameter *uid-index* (create-uid-index *uid-sorted*)))
  (wait-text "Creating title list... "
    (defparameter *title-list* (create-title-list))))

(declaim (inline not-quite-rms-error))
(defun not-quite-rms-error (seq1 seq2)
  (declare (optimize (speed 3) (safety 0)))
  (sqrt (the fixnum (reduce '+ (map 'vector #'(lambda(x y)
						(declare (fixnum x y))
						(the fixnum (expt (the fixnum (- x y)) 2)))
				    seq1 seq2)))))

(defun double-mid-extracting-fast-intersection (seq-bounds1 seq-bounds2)
  (declare (optimize (speed 3) (safety 0))
	   (simple-array seq-bounds1 seq-bounds2))
  "Need to get the mid out of a full rating to use as a key, but push the 
  stars. Faster to get the stars now, since we already have the rating, than
  to map over the sequence later and extract them.

  Returns two lists - stars from set1 and stars from set2. They have mids in common,
  but different stars, so we need to keep them separate.

  Each parameter is a vector of the lower and upper bound, within *uid-sorted*, of
  a users ratings. Faster than creating a displaced array, and this lets us use svref."
  (let ((s1start (svref seq-bounds1 0))
	(s1end (svref seq-bounds1 1))
	(s2start (svref seq-bounds2 0))
	(s2end (svref seq-bounds2 1))
	(common1 nil)
	(common2 nil))
    (declare (fixnum s1start s2start s1end s2end))
    (labels ((intersect-r (s1pos s2pos)
	       (cond ((and (< s1pos s1end) (< s2pos s2end))
		      (let* ((item1 (svref *uid-sorted* s1pos))
			     (item2 (svref *uid-sorted* s2pos))
			     (value1 (extract-mid item1))
			     (value2 (extract-mid item2)))
			(declare (fixnum item1 item2)
				 (fixnum value1 value2))
			(cond ((= value1 value2)
			       (push (the fixnum (extract-stars item1)) common1)
			       (push (the fixnum (extract-stars item2)) common2)
			       (intersect-r (1+ s1pos) (1+ s2pos)))
			      ((< value1 value2)
			       (intersect-r (1+ s1pos) s2pos))
			      (T
			       (intersect-r s1pos (1+ s2pos))))))
		     (T (values common1 common2)))))
      (intersect-r s1start s2start))))

(defun compare-users (uid1 uid2 &optional (ratinglist2 (nfind-ratings-by-uid uid2)))
  (declare (optimize (speed 3) (safety 0))
	   (fixnum uid1 uid2))
  "Finds the ratings for the movies the users have in common, extracts the stars, then calculates
  the rms error (almost) for them. Faster than the old version which required two passes of
  finding all movies a user had rated - this one does it once. Caller can still pass in ratings
  by the second user as a vector."

  ;; No longer check if uids are identical
  (let ((ratinglist1 (nfind-ratings-by-uid uid1)))
    (multiple-value-bind (rintersection1 rintersection2)
	(double-mid-extracting-fast-intersection ratinglist1 ratinglist2)
      (let ((rmse (not-quite-rms-error rintersection1 rintersection2)))	;inlined - counts against this fn's time
	(declare (single-float rmse))
	(when (zerop rmse) (setf rmse 0.1)) ;tune this - right now, if all ratings are the same, that's worth 10x
	(/ (length rintersection1) rmse))))) ;tune this - formula could be anything where higher = better

(defun restrict-length (seq maxlen)
  (declare (optimize (speed 3) (safety 0))
	   (fixnum maxlen)
	   (simple-array seq))
  (let ((len (length seq)))
    (declare (fixnum len))
    (cond ((<= len maxlen) seq)
	  (T				;Knuth's Algorithm S - randomized selection
	   (let ((result (make-array maxlen :fill-pointer 0))
		 (n maxlen))
	     (declare (fixnum n))
	     (loop for seen fixnum from 0
		   when (< (* (- len seen) (random 1.0)) n)
		   do
		   (vector-push (svref seq seen) result)
		   (decf n)
		   until (zerop n))
	     result)))))

(defun find-best-correlations (uid other-uids)
  (declare (optimize (speed 3) (safety 0))
	   (fixnum uid))
  "Returns a vector of #(rms-error uid), sorted by rmse, decreasing"
  (let* ((rating-list (nfind-ratings-by-uid uid))
	 (correlations (map 'vector #'(lambda(cur-uid) 
					(vector (compare-users cur-uid uid rating-list) cur-uid)) 
			    ;(restrict-length other-uids *max-sequence-length*))))
			    other-uids)))
    (sort correlations '> :key #'(lambda(x) (svref x 0)))))

(defun predict-user-rating (uid mid &optional (users-who-rated (find-users-who-rated mid)))
  (let* ((others-who-rated (remove uid users-who-rated :count 1))
	 (full-correlations (find-best-correlations uid others-who-rated))
	 (best-correlations (subseq full-correlations 0 (min *num-of-correlations* (length full-correlations))))
	 (rmse-sum (reduce '+ best-correlations :key #'(lambda(x) (svref x 0))))
	 (predicted-rating 0))
    (loop for i across best-correlations
	  do
	  (incf predicted-rating (* (svref i 0) (extract-stars (find-rating-by-mid-and-uid mid (svref i 1))))))
    (cond ((zerop rmse-sum) (average-movie-stars mid))
	   (T 
	    (let ((rating (float (/ predicted-rating rmse-sum))))
	      (cond ((> rating 5.0) 5.0)
		    (T rating)))))))

(defun process-datafile (datafile &key (count 100) (nolimit nil) (outfile "probe-output.txt"))
  (unless *mid-sorted* (load-all-files))
  (let ((cur-mid 0)
	(users-who-rated nil)
	(total-error 0)
	(num-processed 0))
    (with-open-file (s datafile)
      (with-open-file (out outfile
		       :direction :output
		       :if-exists :supersede)
	(loop for line = (read-line s nil nil)
	      while (and line
			 (or nolimit
			     (< num-processed count)))
	      do
	      (cond  ((find #\: line)
		      (setf cur-mid (parse-integer line :junk-allowed t))
		      (setf users-who-rated (find-users-who-rated cur-mid))
		      (format t "~a:~%" cur-mid)
		      (format out "~a:~%" cur-mid))
		     (T
		      (let* ((uid (parse-integer line :junk-allowed t))
			     (predicted (predict-user-rating uid cur-mid users-who-rated))
			     (actual (extract-stars (find-rating-by-mid-and-uid cur-mid uid))))
			     ;(actual 0))
			(incf total-error (expt (- predicted actual) 2))
			(incf num-processed)
			(unless nolimit
			  (format t "~a~,7@t~a~,17@t~a~,15@t~a~,5@t~a~,15t~a~%" cur-mid uid predicted actual (sqrt (/ total-error num-processed)) num-processed))
			(format out "~a~%" predicted))))))
      
      (format t "RMSE: ~a~%" (sqrt (/ total-error count))))))

(defun average-movie-stars (mid)
  (float (/ (reduce '+ (map 'vector 'extract-stars (find-ratings-by-mid mid))) (num-ratings-by-mid mid))))

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


;; No longer used

;; (defun get-mids-from-user (uid)
;;   (declare (optimize (speed 3) (safety 0))
;; 	   (fixnum uid))
;;   (map 'list 'extract-mid (find-ratings-by-uid uid)))

;; (defun get-mids-with-stars-from-user (uid)
;;   (map 'list #'(lambda(x) (vector (extract-mid x) (extract-stars x))) (find-ratings-by-uid uid)))

;; (defun fast-intersection (seq1 seq2)
;;   (declare (optimize (speed 3) (safety 0)))
;;   ;; assumes both sequences are lists sorted in ascending order
;;   (let ((common nil))
;;     (labels ((intersect-r (seq1 seq2)
;; 	       (cond ((and seq1 seq2)
;; 		      (let ((item1 (car seq1))
;; 			    (item2 (car seq2)))
;; 			(declare (fixnum item1) (fixnum item2))
;; 			(cond ((= item1 item2)
;; 			       (push item1 common)
;; 			       (intersect-r (cdr seq1) (cdr seq2)))
;; 			      ((< item1 item2)
;; 			       (intersect-r (cdr seq1) seq2))
;; 			      ((> item1 item2)
;; 			       (intersect-r seq1 (cdr seq2))))))
;; 		     (T (nreverse common)))))
;;       (intersect-r seq1 seq2))))
	  
;; (defun mid-extracting-fast-intersection (mids ratings)
;;   (declare (optimize (speed 3) (safety 0)))
;;   "Need to get the mid out of a full rating (ratings) to use as a key, but push the 
;;   whole rating, since it contains stars.

;;   assumes both sequences are lists sorted in ascending order"
;;   (let ((common nil))
;;     (labels ((intersect-r (seq1 seq2)
;; 	       (cond ((and seq1 seq2)
;; 		      (let* ((item1 (car seq1))
;; 			     (item2 (car seq2))
;; 			     (value2 (extract-mid item2)))
;; 			(declare (fixnum item1) (fixnum item2) (fixnum value2))
;; 			(cond ((= item1 value2)
;; 			       (push item2 common)
;; 			       (intersect-r (cdr seq1) (cdr seq2)))
;; 			      ((< item1 value2)
;; 			       (intersect-r (cdr seq1) seq2))
;; 			      ((> item1 value2)
;; 			       (intersect-r seq1 (cdr seq2))))))
;; 		     (T common))))	;forward/reversed not important, so cycle-shave by not reversing
;;       (intersect-r mids ratings))))

;; (defun non-star-pushing-double-mid-extracting-fast-intersection (ratings1 ratings2)
;;   (declare (optimize (speed 3) (safety 0)))
;;   "Need to get the mid out of a full rating to use as a key, but push the 
;;   whole rating, since it contains stars.

;;   Returns two lists - ratings from set1 and ratings from set2. They have mids in common,
;;   but different stars, so we need to keep them separate.

;;   assumes both sequences are lists sorted in ascending order"
;;   (let ((common1 nil)
;; 	(common2 nil))
;;     (labels ((intersect-r (seq1 seq2)
;; 	       (cond ((and seq1 seq2)
;; 		      (let* ((item1 (car seq1))
;; 			     (item2 (car seq2))
;; 			     (value1 (extract-mid item1))
;; 			     (value2 (extract-mid item2)))
;; 			(declare (fixnum item1 item2)
;; 				 (fixnum value1 value2))
;; 			(cond ((= value1 value2)
;; 			       (push item1 common1)
;; 			       (push item2 common2)
;; 			       (intersect-r (cdr seq1) (cdr seq2)))
;; 			      ((< value1 value2)
;; 			       (intersect-r (cdr seq1) seq2))
;; 			      (T
;; 			       (intersect-r seq1 (cdr seq2))))))
;; 		     (T (values common1 common2)))))
;;       (intersect-r ratings1 ratings2))))

;; (defun stock-double-mid-extracting-fast-intersection (seq1 seq2)
;;   (declare (optimize (speed 3) (safety 0))
;; 	   (simple-array seq1 seq2))
;;   "Need to get the mid out of a full rating to use as a key, but push the 
;;   stars. Faster to get the stars now, since we already have the rating, than
;;   to map over the sequence later and extract them.

;;   Returns two lists - stars from set1 and stars from set2. They have mids in common,
;;   but different stars, so we need to keep them separate.

;;   assumes both sequences are vectors sorted in ascending order"
;;   (let ((s1len (length seq1))
;; 	(s2len (length seq2))
;; 	(common1 nil)
;; 	(common2 nil))
;;     (labels ((intersect-r (s1pos s2pos)
;; 	       (cond ((and (< s1pos s1len) (< s2pos s2len))
;; 		      (let* ((item1 (svref seq1 s1pos))
;; 			     (item2 (svref seq2 s2pos))
;; 			     (value1 (extract-mid item1))
;; 			     (value2 (extract-mid item2)))
;; 			(declare (fixnum item1 item2)
;; 				 (fixnum value1 value2))
;; 			(cond ((= value1 value2)
;; 			       (push (the fixnum (extract-stars item1)) common1)
;; 			       (push (the fixnum (extract-stars item2)) common2)
;; 			       (intersect-r (1+ s1pos) (1+ s2pos)))
;; 			      ((< value1 value2)
;; 			       (intersect-r (1+ s1pos) s2pos))
;; 			      (T
;; 			       (intersect-r s1pos (1+ s2pos))))))
;; 		     (T (values common1 common2)))))
;;       (intersect-r 0 0))))

;; (defun fast-find (target sequence key-function)
;;   (declare (optimize (speed 3) (safety 0))
;; 	   (fixnum target) (function key-function))
;;   ;; loop over sequence looking for target. return target if we find it.
;;   ;; as soon as we find an item larger than target, abort.
;;   ;; assumes sequence is sorted in ascending order
;;   (loop for i fixnum in sequence
;; 	do
;; 	(cond ((= i (the fixnum (funcall key-function target))) (return-from fast-find target))
;; 	      ((> i (the fixnum (funcall key-function target))) (return-from fast-find nil)))))

;; (defun slow-get-user-ratings (uid mids)
;;   ;; Get all ratings by this user, remove those whose mid value can't be found
;;   ;; in the list passed in. Slow. *FIXME* get all-ratings as a list and use fast-intersection
;;   (let* ((all-ratings (find-ratings-by-uid uid)) ;all ratings by this user, including movies we're not interested in
;; 	 (ratings (remove-if-not #'(lambda(x) (fast-find x mids #'extract-mid)) all-ratings)))
;;     (map 'vector 'extract-stars ratings)))

;; (defun get-user-ratings (uid mids)
;;   "Get all ratings by this user, and intersect their mids with the mids
;;   in the list passed in. Faster.

;;   No longer needed - we do most of the work in compare-users, now."
;;   (let* ((all-ratings (map 'list 'identity (find-ratings-by-uid uid))) ;all ratings, including movies we're not interested in
;; 	 (ratings (mid-extracting-fast-intersection mids all-ratings)))
;;     (map 'vector 'extract-stars ratings)))

;; (defun mid/ratings-accepting-compare-users (uid1 uid2 &optional (mlist2 (get-mids-from-user uid2)))
;;   (declare (optimize (speed 3) (safety 0))
;; 	   (fixnum uid1) (fixnum uid2))
;;   "Find movies users have in common, get the ratings for them in matching vectors,
;;   then calculate the rms error of the vectors

;;   Typically called many times in a row with the same uid2, so the caller 
;;   has the option of pre-computing mlist2"
;;   (when (= uid1 uid2)
;;     (return-from mid/ratings-accepting-compare-users 0))
;;   (let* ((mlist1 (get-mids-from-user uid1))
;; 	 (common-mids (fast-intersection mlist1 mlist2)))
;;     (let* ((ratings1 (get-user-ratings uid1 common-mids))
;; 	   (ratings2 (get-user-ratings uid2 common-mids))
;; 	   (rmse (not-quite-rms-error ratings1 ratings2)))
;;       (declare (single-float rmse))
;;       (when (zerop rmse) (setf rmse 0.1)) ;tune this - right now, if all ratings are the same, that's worth 10x
;;       (float (/ (length common-mids) rmse))))) ;tune this - formula could be anything where higher = better

;; (defun non-star-getting-compare-users (uid1 uid2 &optional (ratinglist2 (map 'list 'identity (find-ratings-by-uid uid2))))
;;   (declare (optimize (speed 3) (safety 0))
;; 	   (fixnum uid1 uid2))
;;   "Finds the ratings for the movies the users have in common, extracts the stars, then calculates
;;   the rms error (almost) for them. Faster than the old version which required two passes of
;;   finding all movies a user had rated - this one does it once. Caller can still pass in ratings
;;   by the second user - as a list now, not a vector."

;;   ;; No longer check if uids are identical
;;   (let ((ratinglist1 (map 'list 'identity (find-ratings-by-uid uid1))))
;;     (multiple-value-bind (rintersection1 rintersection2) 
;; 	(double-mid-extracting-fast-intersection ratinglist1 ratinglist2)
;;       (let* ((ratings1 (map 'vector 'extract-stars rintersection1))
;; 	     (ratings2 (map 'vector 'extract-stars rintersection2))
;; 	     (rmse (not-quite-rms-error ratings1 ratings2)))
;; 	(declare (single-float rmse))
;; 	(when (zerop rmse) (setf rmse 0.1)) ;tune this - right now, if all ratings are the same, that's worth 10x
;; 	(/ (length ratings1) rmse))))) ;tune this - formula could be anything where higher = better

;; (defun vector-push-find-best-correlations (uid other-uids)
;;   "Returns a vector of #(rms-error uid), sorted by rmse, decreasing"
;;   (let ((correlations (make-array (length other-uids) :fill-pointer 0))
;; 	(movie-list (get-mids-from-user uid)))
;;     ;(loop for cur-uid across (restrict-length other-uids *max-sequence-length*)
;;     (loop for cur-uid across other-uids
;; 	  do
;; 	  (vector-push (vector (compare-users cur-uid uid movie-list) cur-uid) correlations))
;;     (sort correlations '> :key #'(lambda(x) (aref x 0)))))

;; (defun non-star-using-find-best-correlations (uid other-uids)
;;   (declare (optimize (speed 3) (safety 0))
;; 	   (fixnum uid))
;;   "Returns a vector of #(rms-error uid), sorted by rmse, decreasing"
;;   (let* ((rating-list (map 'list 'identity (find-ratings-by-uid uid)))
;; 	 (correlations (map 'vector #'(lambda(cur-uid) 
;; 					(vector (non-star-getting-compare-users cur-uid uid rating-list) cur-uid)) 
;; 			    ;(restrict-length other-uids *max-sequence-length*))))
;; 			    other-uids)))
;;     (sort correlations '> :key #'(lambda(x) (svref x 0)))))

;; (defun non-star-using-predict-user-rating (uid mid &optional (users-who-rated (find-users-who-rated mid)))
;;   (let* ((others-who-rated (remove uid users-who-rated :count 1))
;; 	 (full-correlations (non-star-using-find-best-correlations uid others-who-rated))
;; 	 (best-correlations (subseq full-correlations 0 (min *num-of-correlations* (length full-correlations))))
;; 	 (rmse-sum (reduce '+ best-correlations :key #'(lambda(x) (svref x 0))))
;; 	 (predicted-rating 0))
;;     (loop for i across best-correlations
;; 	  do
;; 	  (incf predicted-rating (* (svref i 0) (extract-stars (find-rating-by-mid-and-uid mid (svref i 1))))))
;;     (cond ((zerop rmse-sum) (average-movie-stars mid))
;; 	   (T 
;; 	    (let ((rating (float (/ predicted-rating rmse-sum))))
;; 	      (cond ((> rating 5.0) 5.0)
;; 		    (T rating)))))))

