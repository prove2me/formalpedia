-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_supergraph_with_triangulated_edge_count
-- name    : WilliamsonShmoys.drawable_supergraph_with_triangulated_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:57:47.758962+00:00
-- url     : https://prove2.me/theorems/b20803f2-ba1d-4792-8629-bbbc0caa0274
-- title:
--   Triangulated completion of a drawable graph
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertices whose edge count is 3n−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_supergraph_with_triangulated_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn J)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, J.edgeSet ⊆ K.edgeSet ∧
      HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
