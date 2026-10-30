-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_upper_bound_face_count_data_planar_edge_bound_for_face_count_data
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_upper_bound_face_count_data_planar_edge_bound_for_face_count_data
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:13:24.986444+00:00
-- url     : https://prove2.me/theorems/7a092879-d6e6-4652-8a2e-7112c6824a8a
-- title:
--   Planar drawing edge bound for face-count data
-- statement:
--   A finite connected simple graph with at least three vertices and the supplied crossing-free drawing has at most 3n − 6 edges. This is the substantive planar-topology step needed by the parent; the bound includes the sharp triangular case n = 3.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_edge_upper_bound_face_count_data_planar_edge_bound_for_face_count_data
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    K.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
