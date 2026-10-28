-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_has_triangulating_supergraph
-- name    : WilliamsonShmoys.drawable_has_triangulating_supergraph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T17:00:06.037613+00:00
-- url     : https://prove2.me/theorems/d4a7b1db-bf31-4c4d-a988-78948aa0997a
-- title:
--   Drawable graphs extend to a graph with at least the triangulation edge count
-- statement:
--   Any drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with at least 3|V|−6 edges. This is the augmentation half of the planar maximality argument. A proof route is to extend the drawing by noncrossing edges until no further edge can be added, then use the face structure of the resulting maximal embedding; formalizing this from the arc-based drawing predicate is the main work. The size hypothesis rules out the small-order exceptions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_has_triangulating_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ H : SimpleGraph V, U ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
