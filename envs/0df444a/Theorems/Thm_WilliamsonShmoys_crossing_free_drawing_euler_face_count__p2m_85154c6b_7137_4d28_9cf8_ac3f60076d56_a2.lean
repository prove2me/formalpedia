-- Prove2me | Theorems.Thm_WilliamsonShmoys_crossing_free_drawing_euler_face_count__p2m_85154c6b_7137_4d28_9cf8_ac3f60076d56_a2
-- name    : WilliamsonShmoys.crossing_free_drawing_euler_face_count__p2m_85154c6b_7137_4d28_9cf8_ac3f60076d56_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:42:55.154542+00:00
-- url     : https://prove2.me/theorems/c89761fc-1b15-411c-9c3b-7aaa8876b22d
-- title:
--   Euler face count for a connected crossing-free drawing
-- statement:
--   A finite connected graph with a crossing-free drawing has a natural-number face count satisfying Euler's formula. This isolates the topological Euler characteristic argument; a proof route is to formalize the regions and boundary walk count of the given drawing and apply the planar Euler formula. It removes the face-count existence and Euler equation from the parent. The remaining core obligation is connecting the drawing predicate to that topological count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.crossing_free_drawing_euler_face_count__p2m_85154c6b_7137_4d28_9cf8_ac3f60076d56_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    exists f : Nat, H.edgeSet.ncard + 2 = Fintype.card V + f := by sorry
