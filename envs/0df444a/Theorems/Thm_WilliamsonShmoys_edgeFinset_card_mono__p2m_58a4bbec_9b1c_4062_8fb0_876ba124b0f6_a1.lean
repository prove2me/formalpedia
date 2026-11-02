-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeFinset_card_mono__p2m_58a4bbec_9b1c_4062_8fb0_876ba124b0f6_a1
-- name    : WilliamsonShmoys.edgeFinset_card_mono__p2m_58a4bbec_9b1c_4062_8fb0_876ba124b0f6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:00:07.573384+00:00
-- url     : https://prove2.me/theorems/db94edf3-b784-4947-bdc9-feac394e144d
-- title:
--   Monotonicity of edge count under graph inclusion
-- statement:
--   If every edge of one finite simple graph is an edge of another graph on the same ordered vertex type, the first graph’s edge count is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edgeFinset_card_mono__p2m_58a4bbec_9b1c_4062_8fb0_876ba124b0f6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G K : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel K.Adj]
    (hsub : ∀ u v : V, G.Adj u v → K.Adj u v) :
    G.edgeFinset.card ≤ K.edgeFinset.card := by sorry
