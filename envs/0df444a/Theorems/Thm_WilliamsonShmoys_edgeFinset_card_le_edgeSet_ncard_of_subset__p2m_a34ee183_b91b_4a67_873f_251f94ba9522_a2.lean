-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeFinset_card_le_edgeSet_ncard_of_subset__p2m_a34ee183_b91b_4a67_873f_251f94ba9522_a2
-- name    : WilliamsonShmoys.edgeFinset_card_le_edgeSet_ncard_of_subset__p2m_a34ee183_b91b_4a67_873f_251f94ba9522_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:17:52.015586+00:00
-- url     : https://prove2.me/theorems/93e7a307-df42-4503-a91f-bebecf49e254
-- title:
--   Edge count monotonicity across finite edge representations
-- statement:
--   If K’s edges are included in H’s edge set on a finite vertex type, then K’s finite edge count is at most the cardinality of H’s edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.edgeFinset_card_le_edgeSet_ncard_of_subset__p2m_a34ee183_b91b_4a67_873f_251f94ba9522_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K H : SimpleGraph V) [DecidableRel K.Adj]
    (hKH : K.edgeSet ⊆ H.edgeSet) :
    K.edgeFinset.card ≤ H.edgeSet.ncard := by
  sorry
