-- Prove2me | Theorems.Thm_SubquadCutReach_Faster_lemma_2_4
-- name    : SubquadCutReach.Faster.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T17:03:32.428599+00:00
-- url     : https://prove2.me/theorems/bf2253c3-a8aa-4bd1-8374-c60e8bfeafe1
-- title:
--   Lemma 2.4 — Operations on subgraphs
-- statement:
--   Let $H$ be a hidden simple graph on $n$ labelled vertices and let $P$ be a known family of potential pairs. Put $E(J)=E(H)\cap P$. There are uniform deterministic cut-oracle programs which count or find neighbours in any candidate set excluding its vertex, count all edges, enumerate them explicitly, and return a spanning forest.
--
--   $$Q_{\rm count}\le C,\quad Q_{\rm search}\le CL(n),\quad Q_{\rm edges}\le Cn,\quad Q_{\rm enumerate}\le C(n+|E(J)|)L(n),\quad Q_{\rm forest}\le CnL(n).$$
--
--   A search returns either a genuine neighbour or a certificate of absence. Enumeration returns exactly the edge set, and the forest is acyclic with the same reachability components. Every program receives $P$ and its task data but only a cut oracle for $H$. These are the shared primitives for implicit subgraphs.
--
--   Differences from the source:
--   - encoding: finite labelled oracle inputs and O or Õ bounds → Fin n, finite rational-literal oracle programs, charged queries and outer uniform positive constants; reason: relabeling and an operational cost semantics preserve the source input domain; nontermination has infinite cost
--   - generalization: enumeration with Õ(n + a) queries → at most C(n + a)L(n) queries, a single logarithmic factor; reason: this implies Õ(n + a); the source proof gives a + n successful and unsuccessful searches of O(log n) queries each
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), p. 4, Lemma 2.4 (PDF p. 6)

import Definitions.Def_SubquadCutReach_Faster_Tasks

set_option autoImplicit false
open scoped Classical

namespace SubquadCutReach.Faster

theorem lemma_2_4 :
    ∃ C : ℝ, 0 < C ∧ ∃ Pc Ps Pe Pl Pf : Program,
      (∀ P ∈ [Pc,Ps,Pe,Pl,Pf], Admissible P ∧ Deterministic P) ∧
      ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (P : Rule n),
        let J := subgraph H P
        (∀ (v : Fin n) (X : Finset (Fin n)), v ∉ X →
          RunsWithin Pc (cut H) (subInput P v.val X)
            (fun m => m 0 = ((X.filter fun w => J.Adj v w).card : ℝ)) C ∧
          RunsWithin Ps (cut H) (subInput P v.val X)
            (fun m => (m 0 = 0 ∧ ∀ w ∈ X, ¬ J.Adj v w) ∨
              ∃ w ∈ X, J.Adj v w ∧ m 0 = (w.val+1 : ℕ)) (C*L n)) ∧
        RunsWithin Pe (cut H) (subInput P 0 ∅)
          (fun m => m 0 = ((pairs J).card : ℝ)) (C*n) ∧
        RunsWithin Pl (cut H) (subInput P 0 ∅)
          (fun m => outputPairs n m = pairs J) (C*(n+(pairs J).card)*L n) ∧
        RunsWithin Pf (cut H) (subInput P 0 ∅)
          (fun m => SpanningForest J (outputPairs n m)) (C*n*L n) := by sorry

end SubquadCutReach.Faster
