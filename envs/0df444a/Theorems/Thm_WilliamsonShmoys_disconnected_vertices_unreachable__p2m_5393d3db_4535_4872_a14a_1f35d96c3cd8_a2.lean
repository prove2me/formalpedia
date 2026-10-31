-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_vertices_unreachable__p2m_5393d3db_4535_4872_a14a_1f35d96c3cd8_a2
-- name    : WilliamsonShmoys.disconnected_vertices_unreachable__p2m_5393d3db_4535_4872_a14a_1f35d96c3cd8_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:31:02.575593+00:00
-- url     : https://prove2.me/theorems/85c828ba-fea3-4a9f-a103-019dd890a1ec
-- title:
--   A disconnected graph has distinct unreachable vertices
-- statement:
--   A disconnected finite graph with at least three vertices contains two distinct vertices that are not reachable from one another.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_vertices_unreachable__p2m_5393d3db_4535_4872_a14a_1f35d96c3cd8_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDisc : ¬ M.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ M.Reachable u v := by
  sorry
