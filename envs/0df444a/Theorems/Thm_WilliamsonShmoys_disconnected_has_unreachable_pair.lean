-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_has_unreachable_pair
-- name    : WilliamsonShmoys.disconnected_has_unreachable_pair
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-27T16:17:06.207179+00:00
-- url     : https://prove2.me/theorems/44c1aef5-4145-4e92-be18-b85d403b7d90
-- title:
--   Disconnectedness yields an unreachable pair
-- statement:
--   If a finite graph is not connected, some pair of vertices is not reachable from one another.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_has_unreachable_pair
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDisconnected : ¬ H.Connected) :
    ∃ u v : V, ¬ H.Reachable u v := by sorry
