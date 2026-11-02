-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeFinset_mono__p2m_f073101b_bf91_4d7c_9d90_d062f14a8fca_a1
-- name    : WilliamsonShmoys.edgeFinset_mono__p2m_f073101b_bf91_4d7c_9d90_d062f14a8fca_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:34:20.446819+00:00
-- url     : https://prove2.me/theorems/93abe885-7c1a-419e-96a9-63aa87ecaf1a
-- title:
--   Monotonicity of finite graph edge counts
-- statement:
--   If one finite simple graph is a subgraph of another on the same ordered vertex type, its finite edge count is no greater. This supplies the parent’s passage from the original graph to its triangulated extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edgeFinset_mono__p2m_f073101b_bf91_4d7c_9d90_d062f14a8fca_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (hGH : G ≤ H) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     letI : DecidableRel H.Adj := Classical.decRel H.Adj
     G.edgeFinset.card ≤ H.edgeFinset.card) := by sorry
