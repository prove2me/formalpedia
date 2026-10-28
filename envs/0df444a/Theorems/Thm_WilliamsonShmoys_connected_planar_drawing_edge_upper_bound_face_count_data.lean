-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_upper_bound_face_count_data
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_upper_bound_face_count_data
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T09:57:46.060785+00:00
-- url     : https://prove2.me/theorems/f9042e33-044f-4bd6-bec4-5e0e92f2d3b1
-- title:
--   Euler and face-boundary counts for a connected planar drawing
-- statement:
--   A connected finite simple graph with at least three vertices and the supplied planar drawing has a face count satisfying Euler’s relation and the face-boundary count inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_edge_upper_bound_face_count_data
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f <= 2 * K.edgeSet.ncard := by sorry
