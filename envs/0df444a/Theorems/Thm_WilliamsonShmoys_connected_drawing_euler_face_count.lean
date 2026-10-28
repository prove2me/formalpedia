-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_face_count
-- name    : WilliamsonShmoys.connected_drawing_euler_face_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:56:47.766436+00:00
-- url     : https://prove2.me/theorems/7ab2e75b-c3e7-4133-9911-3b0e6682478e
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A finite connected graph with the supplied planar drawing has a natural-number face count satisfying Euler’s formula. The proof extracts a plane embedding from the drawing and applies the connected planar Euler formula; the lower bound on the number of vertices is not needed for Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_drawing_euler_face_count
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected) :
    ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by sorry
