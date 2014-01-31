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

(defn interp [inst env]
  (println env)
  (match inst
         [:op result op arg rest] (let [arg (resolve arg env)
                                    ret (do-op op arg)
                                    newenv (assoc env result arg)]
                                     (recur rest newenv))

         [:op result op arg1 arg2 rest] (let [arg1 (resolve arg1 env)
                                          arg2 (resolve arg2 env)
                                          ret (do-op op arg1 arg2)
                                          newenv (assoc env result ret)]
                                           (recur rest newenv))

         [:jump blk] (recur (get @*blocks* blk)
                            env)

         [:if test then else] (if (resolve test env)
                                (recur (get @*blocks* then) env)
                                (recur (get @*blocks* else) env))

         [:print-and-stop arg] (println (resolve arg env))))



(def code '{power [:op res same 1
                   [:if y power-rec power-done]]

            power-rec [:op res mul res x
                       [:op y sub y 1
                        [:op cmp ge y 1
                         [:if cmp power-rec power-done]]]]

            power-done [:print-and-stop res]})

(binding [*blocks* (atom code)
          *code-cache* (atom {})]
  (interp (get code 'power) {'x 10 'y 10}))


(defn presolve [x env]
  (if (symbol? x)
    (if (contains? env x)
      (get env x)
      x)
    x))

(declare do-pe)

(defn pe [inst penv]
  (match inst
         [:op resultvar op arg rest]
         (let [arg (presolve arg penv)]
           (if (const? arg)
             (let [result (do-op op arg)
                   nenv (assoc penv resultvar result)]
               (recur rest nenv))
             (let [nenv (dissoc penv resultvar)
                   newrest (pe rest nenv)]
               [:op resultvar op arg newrest])))

         [:op resultvar op arg1 arg2 rest]
         (let [arg1 (presolve arg1 penv)
               arg2 (presolve arg2 penv)]
           (if (and (const? arg1)
                    (const? arg2))
             (let [result (do-op op arg1 arg2)
                   nenv (assoc penv resultvar result)]
               (recur rest nenv))
             (let [nenv (dissoc penv resultvar)
                   newrest (pe rest nenv)]
               [:op resultvar op arg1 arg2 newrest])))

         [:jump block] (let [res (do-pe block penv)]
                         [:jump res])

         [:print-and-stop arg] (let [resolved (presolve arg penv)]
                                 [:print-and-stop resolved])

         [:if test then else] (let [val (if (contains? penv test)
                                          (get penv test)
                                          test)]
                                (if (const? val)
                                  (let [L (if val
                                            then
                                            else)
                                        LR (do-pe L penv)]
                                    [:jump LR])
                                  (let [L1R (do-pe then penv)
                                        L2R (do-pe else penv)]
                                    [:if test L1R L2R])))))


(defn do-pe [L penv]
  (if (contains? @*code-cache* [penv L])
    (get @*code-cache* [penv L])
    (let [LR (gensym "pe_block")]
      (swap! *code-cache* assoc [L penv] LR)
      (let [residual (pe (get @*blocks* L) penv)]
        (swap! *blocks* assoc LR residual)
        LR))))


(binding [*blocks* (atom code)
          *code-cache* (atom {})]
  (let [start-at (do-pe 'power '{y 10 x 10})]
    (println "start at: " start-at)
    (clojure.pprint/pprint @*blocks*)
    (println @*code-cache*)
    (interp (get @*blocks* start-at) '{})))
