-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawingOn_face_count_bounds
-- name    : WilliamsonShmoys.drawingOn_face_count_bounds
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T22:18:14.304626+00:00
-- url     : https://prove2.me/theorems/a7846a2c-8999-4973-90af-8ddd969e3b13
-- title:
--   Face count bounds from a planar drawing
-- statement:
--   For a connected simple graph on at least three vertices with the supplied planar drawing, the number of faces f satisfies Euler’s formula and the sum of face-boundary lengths is at least three per face, counting edge sides with multiplicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawingOn_face_count_bounds {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hconn : G.Connected) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V) : ∃ f : Nat, Fintype.card V + f = G.edgeSet.ncard + 2 ∧ 3 * f ≤ 2 * G.edgeSet.ncard := by sorry
