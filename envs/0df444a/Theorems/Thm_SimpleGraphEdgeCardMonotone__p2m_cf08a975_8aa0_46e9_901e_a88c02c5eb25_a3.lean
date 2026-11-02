-- Prove2me | Theorems.Thm_SimpleGraphEdgeCardMonotone__p2m_cf08a975_8aa0_46e9_901e_a88c02c5eb25_a3
-- name    : SimpleGraphEdgeCardMonotone__p2m_cf08a975_8aa0_46e9_901e_a88c02c5eb25_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:58:35.776018+00:00
-- url     : https://prove2.me/theorems/432c78f3-3edd-4ff0-abcd-bae2b5be5a89
-- title:
--   Edge inclusion controls graph edge counts
-- statement:
--   For finite simple graphs on a finite linearly ordered vertex type, adjacency inclusion gives edgeFinset inclusion and hence nondecreasing cardinality. If reverse adjacency inclusion fails, an edge belongs to K's edgeFinset but not G's, so the inclusion is strict and the cardinality inequality is strict.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem SimpleGraphEdgeCardMonotone__p2m_cf08a975_8aa0_46e9_901e_a88c02c5eb25_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G K : SimpleGraph V)
    (h : ∀ u v, G.Adj u v → K.Adj u v) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     letI : DecidableRel K.Adj := Classical.decRel K.Adj
     G.edgeFinset.card ≤ K.edgeFinset.card) ∧
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     letI : DecidableRel K.Adj := Classical.decRel K.Adj
     (¬ (∀ u v, K.Adj u v → G.Adj u v) →
       G.edgeFinset.card < K.edgeFinset.card)) := by sorry
