-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_face_count_from_arcs_v4
-- name    : WilliamsonShmoys.connected_drawing_euler_face_count_from_arcs_v4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T09:19:41.170066+00:00
-- url     : https://prove2.me/theorems/a0486b27-9837-4c65-93a2-b449728fd1e2
-- title:
--   Euler equation and face-side bound from a connected drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and a drawing by the supplied crossing-free arcs, there is a natural number of faces satisfying Euler’s equation, and three times the face count is at most twice the edge count. The latter counts both sides of every edge, including both occurrences of a bridge on a facial boundary.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_drawing_euler_face_count_from_arcs_v4
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 <= Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f <= 2 * G.edgeSet.ncard := by sorry
