-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_face_degree_bound__p2m_b6befa6f_bbd0_4db9_9632_8e3f38d3e7e4_a1
-- name    : WilliamsonShmoys.connected_planar_drawing_face_degree_bound__p2m_b6befa6f_bbd0_4db9_9632_8e3f38d3e7e4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:52:13.338455+00:00
-- url     : https://prove2.me/theorems/60b0b6c8-2464-4637-be16-9dc08ca4c2cc
-- title:
--   Face-count bound for a connected planar drawing
-- statement:
--   For a connected simple graph with at least three vertices and the supplied planar drawing, any natural face count satisfying the Euler equation obeys 3f ≤ 2|E|. Prove this by counting face-boundary incidences, with each edge counted twice and every face boundary having length at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_face_degree_bound__p2m_b6befa6f_bbd0_4db9_9632_8e3f38d3e7e4_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hconn : G.Connected) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (f : ℕ) (hEuler : Fintype.card V + f = G.edgeSet.ncard + 2) : 3 * f ≤ 2 * G.edgeSet.ncard := by sorry
