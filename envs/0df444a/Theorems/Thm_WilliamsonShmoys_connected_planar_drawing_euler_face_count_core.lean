-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_face_count_core
-- name    : WilliamsonShmoys.connected_planar_drawing_euler_face_count_core
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:46:29.601052+00:00
-- url     : https://prove2.me/theorems/fa87e700-5a7a-430a-a8eb-8a661118af67
-- title:
--   Euler and face count for a connected planar drawing
-- statement:
--   A finite connected simple graph on at least three vertices with the supplied crossing-free drawing has a natural number of faces f satisfying both the Euler equation |V| + f = |E| + 2 and the face-boundary inequality 3f ≤ 2|E|. This packages the drawing-to-plane-embedding, Euler, and boundary-count arguments; the parent follows by arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_euler_face_count_core
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : L.Connected)
    (hdraw : HasPlanarDrawingOn L) :
    ∃ f : ℕ, 3 * f ≤ 2 * L.edgeSet.ncard ∧
      Fintype.card V + f = L.edgeSet.ncard + 2 := by sorry
