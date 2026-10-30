-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_face_count__p2m_5d599c83_54c6_426b_a50f_1d6092e7f607_a2
-- name    : WilliamsonShmoys.connected_planar_drawing_euler_face_count__p2m_5d599c83_54c6_426b_a50f_1d6092e7f607_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T01:02:50.743838+00:00
-- url     : https://prove2.me/theorems/de964016-c5d1-4655-a9b8-5775a5593d8f
-- title:
--   Euler and boundary counts for a connected planar drawing
-- statement:
--   For a connected finite simple graph with at least three vertices and the supplied crossing-free drawing, the embedding has a face count satisfying Euler’s equation, and the sum of face-boundary lengths is twice the edge count with each face boundary of length at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.connected_planar_drawing_euler_face_count__p2m_5d599c83_54c6_426b_a50f_1d6092e7f607_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hConn : H.Connected) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ f : Nat, Fintype.card V + f = H.edgeSet.ncard + 2 ∧ 3 * f ≤ 2 * H.edgeSet.ncard := by sorry
