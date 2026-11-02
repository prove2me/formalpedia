-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_vertices_not_reachable__p2m_8ebe9775_f6af_4eb7_9344_68ad2c5d7599_a4
-- name    : WilliamsonShmoys.disconnected_vertices_not_reachable__p2m_8ebe9775_f6af_4eb7_9344_68ad2c5d7599_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:49:48.957428+00:00
-- url     : https://prove2.me/theorems/567d3188-4520-48b4-aa6f-ad29ef4bdb28
-- title:
--   Disconnected graphs contain a distinct unreachable pair
-- statement:
--   A disconnected graph has distinct vertices that are not reachable from one another.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.disconnected_vertices_not_reachable__p2m_8ebe9775_f6af_4eb7_9344_68ad2c5d7599_a4
    {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (hDisconnected : ¬ N.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ N.Reachable u v := by sorry
