-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound_euler_face_count
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_bound_euler_face_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:25:14.686138+00:00
-- url     : https://prove2.me/theorems/4fedf559-e3b4-4f4d-ace1-0a366264faf3
-- title:
--   Euler face count for the edge bound
-- statement:
--   A connected graph with the specified finite planar drawing has a finite face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_edge_bound_euler_face_count {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hConn : G.Connected) : ∃ f : ℕ, G.edgeSet.ncard + 2 = Fintype.card V + f := by sorry
