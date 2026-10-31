-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_ordered_unreachable__p2m_f5d9ac23_37a8_4813_be64_33098d8dbd1e_a2
-- name    : WilliamsonShmoys.disconnected_ordered_unreachable__p2m_f5d9ac23_37a8_4813_be64_33098d8dbd1e_a2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T06:17:37.652826+00:00
-- url     : https://prove2.me/theorems/4d2fde0b-7ab2-40ba-91e9-e14987f467b1
-- title:
--   Disconnected graph has an ordered unreachable pair
-- statement:
--   A finite disconnected graph on a linearly ordered vertex type has an ordered pair of vertices in distinct reachability classes.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_ordered_unreachable__p2m_f5d9ac23_37a8_4813_be64_33098d8dbd1e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hdis : ¬ K.Connected) :
    ∃ u v : V, u < v ∧ ¬ K.Reachable u v := by
  sorry
