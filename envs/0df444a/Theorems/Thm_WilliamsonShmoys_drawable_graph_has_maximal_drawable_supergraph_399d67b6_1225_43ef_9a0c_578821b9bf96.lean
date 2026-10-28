-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_drawable_supergraph_399d67b6_1225_43ef_9a0c_578821b9bf96
-- name    : WilliamsonShmoys.drawable_graph_has_maximal_drawable_supergraph_399d67b6_1225_43ef_9a0c_578821b9bf96
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:22:43.735628+00:00
-- url     : https://prove2.me/theorems/4d6baac1-79d2-4707-b37b-02f7d5f82680
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every finite drawable simple graph has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs. There are finitely many simple graphs on the finite vertex type, so choose one with a largest edge set among those containing the original graph and admitting a drawing. This removes the finite selection step from the parent; it does not establish an edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_graph_has_maximal_drawable_supergraph_399d67b6_1225_43ef_9a0c_578821b9bf96
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V,
        L.edgeSet ⊆ M.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn M →
        M.edgeSet ⊆ L.edgeSet := by sorry
