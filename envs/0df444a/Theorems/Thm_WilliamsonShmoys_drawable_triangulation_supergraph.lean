-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_triangulation_supergraph
-- name    : WilliamsonShmoys.drawable_triangulation_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:10:32.127965+00:00
-- url     : https://prove2.me/theorems/20e15f2d-7e53-47dd-bb50-add567d01574
-- title:
--   Drawable triangulated supergraph on the same vertices
-- statement:
--   A finite simple drawable graph on at least three vertices is a subgraph of a drawable triangulation on the same vertices, whose edge count is three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_triangulation_supergraph {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hdraw : HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ 3 * Fintype.card V - 6 = L.edgeSet.ncard := by sorry
