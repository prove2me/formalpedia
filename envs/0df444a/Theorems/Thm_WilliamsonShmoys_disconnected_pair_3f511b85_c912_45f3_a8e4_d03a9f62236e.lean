-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_pair_3f511b85_c912_45f3_a8e4_d03a9f62236e
-- name    : WilliamsonShmoys.disconnected_pair_3f511b85_c912_45f3_a8e4_d03a9f62236e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:37:03.412303+00:00
-- url     : https://prove2.me/theorems/32293bb7-c01e-4252-9615-ea64e7330546
-- title:
--   A disconnected graph has an unreachable vertex pair
-- statement:
--   A finite graph with at least two vertices that is not connected has distinct vertices that are not connected by a path.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_pair_3f511b85_c912_45f3_a8e4_d03a9f62236e
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 2 <= Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ G.Reachable u v := by sorry
