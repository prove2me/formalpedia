-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulating_supergraph
-- name    : WilliamsonShmoys.drawable_graph_has_triangulating_supergraph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T14:52:53.573729+00:00
-- url     : https://prove2.me/theorems/ce0b565e-299b-46de-8319-c2e9dc57722f
-- title:
--   Triangulating drawable supergraph
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. This is the triangulation-completion step used by the parent; the construction handles disconnected starting drawings and bridges before applying Euler’s formula to the completed drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_triangulating_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
