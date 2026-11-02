-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeFinset_card_mono__p2m_ad7657d2_129c_4ff8_bf1d_16d96be983d7_a1
-- name    : WilliamsonShmoys.edgeFinset_card_mono__p2m_ad7657d2_129c_4ff8_bf1d_16d96be983d7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:42:11.297202+00:00
-- url     : https://prove2.me/theorems/e3dbae2e-0549-486f-b383-3c86b9f79649
-- title:
--   Monotonicity of finite graph edge counts
-- statement:
--   If every edge of one finite simple graph is an edge of another graph on the same vertex type, then its edge count is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edgeFinset_card_mono__p2m_ad7657d2_129c_4ff8_bf1d_16d96be983d7_a1
    {V : Type} [Fintype V]
    (H G : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hHG : H ≤ G) :
    H.edgeFinset.card ≤ G.edgeFinset.card := by sorry
