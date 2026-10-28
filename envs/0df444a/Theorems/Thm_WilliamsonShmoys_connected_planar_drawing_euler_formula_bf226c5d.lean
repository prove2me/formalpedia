-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_formula_bf226c5d
-- name    : WilliamsonShmoys.connected_planar_drawing_euler_formula_bf226c5d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:42:06.737646+00:00
-- url     : https://prove2.me/theorems/accca68e-5752-42e9-a400-6f058460c8cd
-- title:
--   Euler formula for a connected planar drawing
-- statement:
--   A finite connected simple graph with the specified crossing-free drawing has a natural face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.connected_planar_drawing_euler_formula_bf226c5d
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hConnected : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by sorry
