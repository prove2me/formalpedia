-- Prove2me | Theorems.Thm_SimpleGraph_buildEdgeList_preserves__p2m_7e139eb9_902e_43ae_a2cc_5a720eb5726b_a2
-- name    : SimpleGraph.buildEdgeList_preserves__p2m_7e139eb9_902e_43ae_a2cc_5a720eb5726b_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:18:07.94584+00:00
-- url     : https://prove2.me/theorems/f83a85b8-47b0-4a95-873c-576388ebd17e
-- title:
--   Invariant preserved by permitted edge insertions
-- statement:
--   Starting from any subgraph of G satisfying P, folding a list of increasing-endpoint edges of G preserves P. The proof proceeds by list induction, maintaining that each intermediate graph is a subgraph of G.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Operations

theorem SimpleGraph.buildEdgeList_preserves__p2m_7e139eb9_902e_43ae_a2cc_5a720eb5726b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hzero : P ⊥)
    (hadd : ∀ (K : SimpleGraph V), K ≤ G →
      ∀ u v : V, u < v → G.Adj u v → ¬ K.Adj u v →
      P K → P (K ⊔ SimpleGraph.edge u v)) :
    ∀ (H : SimpleGraph V), H ≤ G → P H →
    ∀ es : List (V × V),
      (∀ p, p ∈ es → p.1 < p.2 ∧ G.Adj p.1 p.2) →
      P (es.foldl (fun K p => K ⊔ SimpleGraph.edge p.1 p.2) H) := by sorry
