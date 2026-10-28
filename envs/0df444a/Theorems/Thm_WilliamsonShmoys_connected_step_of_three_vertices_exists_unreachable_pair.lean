-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_step_of_three_vertices_exists_unreachable_pair
-- name    : WilliamsonShmoys.connected_step_of_three_vertices_exists_unreachable_pair
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:18:19.057163+00:00
-- url     : https://prove2.me/theorems/fe991816-f5c0-44e0-a1ad-cc59f118416e
-- title:
--   A disconnected graph with at least three vertices has an unreachable pair
-- statement:
--   A finite graph with at least three vertices that is disconnected has two unreachable vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_step_of_three_vertices_exists_unreachable_pair
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ u v : V, ¬ G.Reachable u v := by sorry
