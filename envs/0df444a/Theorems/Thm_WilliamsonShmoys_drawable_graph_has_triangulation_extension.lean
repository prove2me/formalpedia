-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulation_extension
-- name    : WilliamsonShmoys.drawable_graph_has_triangulation_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T13:11:47.497849+00:00
-- url     : https://prove2.me/theorems/05af9a75-ca19-4a9c-8179-dbe048e5bffa
-- title:
--   Extend a drawable graph to a triangulation
-- statement:
--   Any graph with a crossing-free drawing on a finite ordered vertex type of size at least three has a drawable supergraph on the same vertex type with exactly the triangulation edge count. This packages the geometric extension and Euler-counting work needed by the parent; the parent uses maximality only to identify that supergraph with K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
