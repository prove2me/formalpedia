-- Prove2me | Theorems.Thm_WilliamsonShmoys_component_edges_le_sum__p2m_666f06c4_d624_4127_b254_b308e951621e_a1
-- name    : WilliamsonShmoys.component_edges_le_sum__p2m_666f06c4_d624_4127_b254_b308e951621e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:10:08.557324+00:00
-- url     : https://prove2.me/theorems/dba7ffb5-b08a-47c1-8b40-5eb84dde2b1d
-- title:
--   Bound graph edges by the sum of component edges
-- statement:
--   The total number of edges is at most the sum of the numbers of edges in the induced graphs on the connected component supports. Every edge has both endpoints in the same connected component.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.component_edges_le_sum__p2m_666f06c4_d624_4127_b254_b308e951621e_a1
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) :
    letI : Fintype K.ConnectedComponent := Fintype.ofFinite _
    letI : (L : SimpleGraph V) → DecidableRel L.Adj := fun L => Classical.decRel L.Adj
    K.edgeFinset.card ≤ ∑ c : K.ConnectedComponent,
      (letI : Fintype {v : V // v ∈ c.supp} := Fintype.ofFinite _
       letI : DecidableRel ((K.induce c.supp).Adj) := Classical.decRel _
       (K.induce c.supp).edgeFinset.card) := by sorry
