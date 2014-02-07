(ns jit-playground.core
  (:refer-clojure :exclude [resolve])
  (:require [clojure.core.match :refer [match]]))

(defn const? [x]
  (not (symbol? x)))

(defn resolve [arg env]
  (if (symbol? arg)
    (if (contains? env arg)
      (get env arg)
      (assert false (str "could not resolve " arg " in " env)))
    arg))

(defn do-op [& args]
  (match (vec args)
         ['same X] X
         ['mul X Y] (* X Y)
         ['add X Y] (+ X Y)
         ['sub X Y] (- X Y)
         ['div X Y] (/ X Y)
         ['eq x y] (= x y)
         ['ge x y] (>= x y)))

(def ^:dynamic *blocks*)
(def ^:dynamic *code-cache*)

(defn interp [block ip env]
  (println env)
  (let [inst (nth block ip)]
    (match inst
           [:op result op arg] (let [arg (resolve arg env)
                                     ret (do-op op arg)
                                     newenv (assoc env result arg)]
                                 (recur block (inc ip) newenv))

           [:op result op arg1 arg2] (let [arg1 (resolve arg1 env)
                                           arg2 (resolve arg2 env)
                                           ret (do-op op arg1 arg2)
                                           newenv (assoc env result ret)]
                                       (recur block (inc ip) newenv))

           [:jump blk] (recur (get @*blocks* blk)
                              0
                              env)

           [:if test then else] (if (resolve test env)
                                  (recur (get @*blocks* then) 0 env)
                                  (recur (get @*blocks* else) 0 env))

           [:print-and-stop arg] (println (resolve arg env))

           [:guard-value sym val blk] (let [rsym (resolve sym env)]
                                        (if (= rsym val)
                                          (recur block (inc ip) env)
                                          (recur (get @*blocks* blk) 0 env)))

           [:guard-true sym blk] (let [rsym (resolve sym env)]
                                        (if rsym
                                          (recur block (inc ip) env)
                                          (recur (get @*blocks* blk) 0 env)))

           [:loop] (recur block 0 env))))



(def code '{power [[:op res same 1]
                   [:if y power-rec power-done]]

            power-rec [[:op res mul res x]
                       [:op y sub y 1]
                       [:op cmp ge y 1]
                       [:if cmp power-rec power-done]]

            power-done [[:print-and-stop res]]})

(binding [*blocks* (atom code)
          *code-cache* (atom {})]
  (interp (get code 'power) 0 {'x 10 'y 10}))


(defn presolve [x env]
  (if (symbol? x)
    (if (contains? env x)
      (get env x)
      x)
    x))

(declare do-pe)

(defn pe [block ip penv new-block]
  (let [inst (nth block ip)]
    (match inst
           [:op resultvar op arg]
           (let [arg (presolve arg penv)]
             (if (const? arg)
               (let [result (do-op op arg)
                     nenv (assoc penv resultvar result)]
                 (recur block (inc ip) nenv new-block))
               (let [nenv (dissoc penv resultvar)]
                 (recur block
                        (inc ip)
                        nenv
                        (conj new-block [:op resultvar op arg])))))

           [:op resultvar op arg1 arg2]
           (let [arg1 (presolve arg1 penv)
                 arg2 (presolve arg2 penv)]
             (if (and (const? arg1)
                      (const? arg2))
               (let [result (do-op op arg1 arg2)
                     nenv (assoc penv resultvar result)]
                 (recur block (inc ip) nenv new-block))
               (let [nenv (dissoc penv resultvar)
                     newrest (pe rest nenv)]
                 (recur block
                        (inc ip)
                        nenv
                        (conj new-block [:op resultvar op arg1 arg2])))))



           [:jump block] (let [res (do-pe block penv)]
                           (conj new-block [:jump res]))

           [:print-and-stop arg] (let [resolved (presolve arg penv)]
                                   (conj new-block [:print-and-stop resolved]))

           [:if test then else] (let [val (if (contains? penv test)
                                            (get penv test)
                                            test)]
                                  (if (const? val)
                                    (let [L (if val
                                              then
                                              else)
                                          LR (do-pe L penv)]
                                      (conj new-block [:jump LR]))
                                    (let [L1R (do-pe then penv)
                                          L2R (do-pe else penv)]
                                      (conj new-block [:if test L1R L2R])))))))


(defn do-pe [L penv]
  (if (contains? @*code-cache* [penv L])
    (get @*code-cache* [penv L])
    (let [LR (gensym "pe_block")]
      (swap! *code-cache* assoc [L penv] LR)
      (let [residual (pe (get @*blocks* L) 0 penv [])]
        (swap! *blocks* assoc LR residual)
        LR))))


(binding [*blocks* (atom code)
          *code-cache* (atom {})]
  (let [start-at (do-pe 'power '{y 10 x 10})]
    (println "start at: " start-at)
    (clojure.pprint/pprint @*blocks*)
    (println @*code-cache*)
    (interp (get @*blocks* start-at) 0 '{})))


;; TODO:
(defn do-optimize [block]
  block)

(defn assert-trace [trace]
  (let [block-name (gensym "trace_")]
    (swap! *blocks* assoc block-name trace)
    block-name))


(defn trace [block ip env start-block trace-data]
  (println env ip block)
  (let [inst (nth block ip)]
    (match inst
           [:op result op arg] (let [rarg (resolve arg env)
                                          ret (do-op op rarg)
                                          newenv (assoc env result arg)]
                                 (recur block (inc ip) newenv start-block
                                        (conj trace-data inst)))

           [:op result op arg1 arg2] (let [rarg1 (resolve arg1 env)
                                           rarg2 (resolve arg2 env)
                                           ret (do-op op rarg1 rarg2)
                                           newenv (assoc env result ret)]
                                       (recur block (inc ip) newenv start-block
                                              (conj trace-data inst)))

           [:jump blk] (if (= blk start-block)
                         ;; trace is completed
                         (let [trace-data (conj trace-data [:loop])]
                           (println trace-data)
                           {:mode :interp
                            :block (assert-trace trace-data)
                            :env  env})
                         ; continue the trace
                         (recur (get @*blocks* blk)
                                  0
                                  env
                                  start-block
                                  trace-data))

           [:if test then else] (let [rtest (resolve test env)
                                      jump-block (if rtest then else)
                                      guard-type (if rtest :guard-true :guard-false)
                                      guard-block (if rtest else then)
                                      trace-data (conj trace-data
                                                       [guard-type test guard-block])]
                                  (if (= jump-block start-block)
                                    (let [trace-data (conj trace-data [:loop])]
                                      (println "trace" trace-data)
                                      {:mode :interp
                                       :block (assert-trace trace-data)
                                       :env env})
                                    (let []
                                      (recur jump-block 0 env start-block
                                             (conj trace-data [:loop])))))

           [:print-and-stop arg] (println (resolve arg env))

           [:promote val dest-blk] (let [rval (get env val)]
                                     (recur (get @*blocks* dest-blk)
                                            0
                                            env
                                            start-block
                                            (conj trace-data
                                                  [:guard-value val rval dest-blk]))))))

(def ^:dynamic *block-counts*)
(def ^:dynamic *already-traced*)
(def ^:dynamic *trace-threshold*)


(def larger-code
  '{l [[:op c ge i 0]
       [:if c b l-done]]

    l-done [[:print-and-stop i]]

    b [[:promote x b2]]

    b2 [[:op x2 mul x 2]
        [:op x3 add x2 1]
        [:op i sub i x3]
        [:jump l]]})

(binding [*blocks* (atom larger-code)
          *code-cache* (atom {})
          *block-counts* (atom {})
          *already-traced* (atom #{})
          ]
  (let [{:keys [block env]} (trace (get @*blocks* 'b) 0 {'i 100 'x 5} 'b [])]
            (interp (get @*blocks* block) 0 env)
            (clojure.pprint/pprint @*blocks*)))

(declare generate-assignments)

(defn optimize [trace penv new-block]
  (let [inst (first trace)]
    (match inst
           [:op resultvar op arg] (let [rarg (presolve arg penv)]
                                    (if (const? rarg)
                                      (let [res (do-op [op arg])
                                            newenv (assoc penv resultvar res)]
                                        (recur (next trace)
                                               newenv
                                               new-block))
                                      (let [newenv (dissoc penv resultvar)]
                                        (recur (next trace)
                                               newenv
                                               (conj new-block
                                                     [:op resultvar op rarg])))))

           [:op resultvar op arg1 arg2] (let [rarg1 (presolve arg1 penv)
                                              rarg2 (presolve arg2 penv)]
                                          (if (and (const? rarg1)
                                                   (const? rarg2))
                                            (let [res (do-op op rarg1 rarg2)
                                                  newenv (assoc penv resultvar res)]
                                              (recur (next trace)
                                                     newenv
                                                     new-block))
                                            (let [newenv (dissoc penv resultvar)]
                                              (recur (next trace)
                                                     newenv
                                                     (conj new-block
                                                           [:op resultvar op rarg1 rarg2])))))

           [:guard-true v block] (let [val (presolve v penv)]
                                   (if (const? val)
                                     (recur (next trace)
                                            penv
                                            new-block)
                                     (recur (next trace)
                                            penv
                                            (conj new-block
                                                  [:guard-true v penv block]))))

           [:guard-false v block] (let [val (presolve v penv)]
                                    (if (const? val)
                                      (recur (next trace)
                                             penv
                                             new-block)
                                      (recur (next trace)
                                             (assoc penv v false)
                                             (conj
                                              new-block
                                              [:guard-false v penv block]))))

           [:guard-value v c block] (let [val (presolve v penv)]
                                      (if (and (const? val)
                                               (= val c))
                                        (recur (next trace)
                                               penv
                                               new-block)
                                        (recur (next trace)
                                               (assoc penv v c)
                                               (conj
                                                new-block
                                                [:guard-value v c penv block]))))

           [:loop] (generate-assignments new-block penv))))


(defn generate-assignments [new-block penv]
  (concat new-block
          (for [[k v] penv]
            [:op k 'same v])))


(binding [*blocks* (atom larger-code)
          *code-cache* (atom {})]
  (let [{:keys [block env]} (trace (get @*blocks* 'b) 0 {'i 100 'x 5} 'b [])
        optimized (optimize (get @*blocks* block) {} [])]
            (interp (get @*blocks* block) 0 env)
            (clojure.pprint/pprint @*blocks*)
            (clojure.pprint/pprint optimized)))
