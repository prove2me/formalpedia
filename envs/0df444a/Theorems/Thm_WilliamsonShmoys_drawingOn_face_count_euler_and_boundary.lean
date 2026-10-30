-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawingOn_face_count_euler_and_boundary
-- name    : WilliamsonShmoys.drawingOn_face_count_euler_and_boundary
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:02:39.516728+00:00
-- url     : https://prove2.me/theorems/fed6f1a3-900d-430a-8b0c-023c8eff9304
-- title:
--   Euler relation and face-boundary count from a planar drawing
-- statement:
--   A connected simple graph with at least three vertices and the supplied crossing-free drawing has a finite face count satisfying Euler’s relation and the lower bound of three on total face-boundary length.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.drawingOn_face_count_euler_and_boundary {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hconn : G.Connected) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V) : ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 ∧ 3 * f ≤ 2 * G.edgeSet.ncard := by sorry
