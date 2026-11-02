-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeFinset_mono__p2m_1ec71208_cc1_45fa_ad3a_a9c7012c7f6f_a3
-- name    : WilliamsonShmoys.edgeFinset_mono__p2m_1ec71208_cc1_45fa_ad3a_a9c7012c7f6f_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:50:20.364518+00:00
-- url     : https://prove2.me/theorems/7f99fa74-7075-4739-9219-03b7af58d123
-- title:
--   Monotonicity of finite simple-graph edge counts
-- statement:
--   For two finite simple graphs on the same vertices, inclusion of the first in the second implies its edge count is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edgeFinset_mono__p2m_1ec71208_cc1_45fa_ad3a_a9c7012c7f6f_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     letI : DecidableRel H.Adj := Classical.decRel H.Adj
     G.edgeFinset.card ≤ H.edgeFinset.card) := by
  sorry
