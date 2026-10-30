-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound_face_degree_bound
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_bound_face_degree_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:30:21.355767+00:00
-- url     : https://prove2.me/theorems/30f0a939-7ff5-40ac-8139-d1b9f0124c83
-- title:
--   Face boundary degree bound for the edge bound
-- statement:
--   For a connected simple graph with at least three vertices and the specified planar drawing, the Euler face count is at most two thirds of the total face-boundary edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_edge_bound_face_degree_bound {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hConn : G.Connected) (hCard : 3 ≤ Fintype.card V) (f : ℕ) (hEuler : G.edgeSet.ncard + 2 = Fintype.card V + f) : 3 * f ≤ 2 * G.edgeSet.ncard := by sorry
