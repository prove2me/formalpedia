-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_face_count__p2m_688f1835_390c_48d2_a756_3ce127433083_a1
-- name    : WilliamsonShmoys.connected_planar_drawing_euler_face_count__p2m_688f1835_390c_48d2_a756_3ce127433083_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:21:30.805692+00:00
-- url     : https://prove2.me/theorems/2ca2cc35-45b9-454e-9480-d6c447ab0740
-- title:
--   Euler face count and boundary incidence bound for a connected planar drawing
-- statement:
--   For a connected simple graph with at least three vertices and a crossing-free drawing, there is a natural-number face count F such that Euler's formula holds and the total face-boundary incidence count implies 3F ≤ 2|E|.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_euler_face_count__p2m_688f1835_390c_48d2_a756_3ce127433083_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     ∃ f : ℕ,
       Fintype.card V + f = H.edgeFinset.card + 2 ∧
       3 * f ≤ 2 * H.edgeFinset.card) := by sorry
