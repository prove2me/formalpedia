-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawing_has_euler_face_count
-- name    : WilliamsonShmoys.connected_drawing_has_euler_face_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T21:46:28.207674+00:00
-- url     : https://prove2.me/theorems/1bb6c4ed-811c-4fc5-b912-ec608fb01f33
-- title:
--   Euler face-count data from a connected planar drawing
-- statement:
--   A finite connected simple graph with at least three vertices and the supplied crossing-free drawing has a natural-number face count satisfying Euler’s equation and the total face-boundary lower bound, expressed as three times the face count being at most twice the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.connected_drawing_has_euler_face_count {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hconn : G.Connected) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V) : ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 ∧ 3 * f ≤ 2 * G.edgeSet.ncard := by sorry
