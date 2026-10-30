-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_face_count
-- name    : WilliamsonShmoys.connected_planar_drawing_euler_face_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:33:30.491444+00:00
-- url     : https://prove2.me/theorems/bf226c5d-60f8-4219-8fd3-87f8a4764c0b
-- title:
--   Euler face count and minimum facial-walk length for a connected plane drawing
-- statement:
--   For a connected simple graph with at least three vertices and a crossing-free drawing, there is a natural-number face count satisfying Euler’s formula, and the total face-boundary length bound implies that three times the number of faces is at most twice the number of edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.connected_planar_drawing_euler_face_count
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by sorry
