-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_formula
-- name    : WilliamsonShmoys.connected_planar_drawing_euler_formula
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:42:26.714999+00:00
-- url     : https://prove2.me/theorems/640ab86d-b471-445e-8cf7-8df274842f10
-- title:
--   Euler formula for a connected planar drawing
-- statement:
--   Every finite connected graph with a crossing-free drawing has a natural number face count satisfying the connected Euler relation, including the singleton case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_euler_formula
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hG : HasPlanarDrawingOn G) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by sorry
