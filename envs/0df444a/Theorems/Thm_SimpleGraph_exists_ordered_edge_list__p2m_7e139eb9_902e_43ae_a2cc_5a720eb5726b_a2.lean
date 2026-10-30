-- Prove2me | Theorems.Thm_SimpleGraph_exists_ordered_edge_list__p2m_7e139eb9_902e_43ae_a2cc_5a720eb5726b_a2
-- name    : SimpleGraph.exists_ordered_edge_list__p2m_7e139eb9_902e_43ae_a2cc_5a720eb5726b_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:18:06.871361+00:00
-- url     : https://prove2.me/theorems/ccb05bbe-990d-4918-abb8-bd955cda86e8
-- title:
--   Finite ordered edge enumeration
-- statement:
--   Every finite simple graph can be reconstructed from the empty graph by inserting a finite list of its edges, with each edge written in increasing endpoint order.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Operations

theorem SimpleGraph.exists_ordered_edge_list__p2m_7e139eb9_902e_43ae_a2cc_5a720eb5726b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) :
    ∃ es : List (V × V),
      (∀ p, p ∈ es → p.1 < p.2 ∧ G.Adj p.1 p.2) ∧
      es.foldl (fun K p => K ⊔ SimpleGraph.edge p.1 p.2) ⊥ = G := by sorry
