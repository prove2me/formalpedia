-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_face_count_core_euler
-- name    : WilliamsonShmoys.connected_planar_drawing_euler_face_count_core_euler
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:55:48.942645+00:00
-- url     : https://prove2.me/theorems/0bcb4241-e893-4948-9ed6-988c9c44c55d
-- title:
--   Euler face count from a connected planar drawing
-- statement:
--   A finite simple connected graph with at least three vertices and the supplied crossing-free drawing has a natural face count satisfying Euler’s equation. This isolates the drawing-to-embedding and Euler-formula work from the parent. A proof route is to construct the plane embedding from the arcs, identify its faces, and apply Euler’s formula for connected plane graphs. The size hypothesis is retained.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_euler_face_count_core_euler
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : L.Connected)
    (hdraw : HasPlanarDrawingOn L) :
    ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 := by sorry
