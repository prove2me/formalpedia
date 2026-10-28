-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_triangulating_supergraph_maximal_extension
-- name    : WilliamsonShmoys.drawable_graph_has_triangulating_supergraph_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:11:48.911373+00:00
-- url     : https://prove2.me/theorems/5a28bf05-b454-4f41-bf90-e6ea5abe7cb0
-- title:
--   Maximal drawable extension for triangulation
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable graph that has no strictly larger drawable supergraph on the same vertices. Prove this by maximizing the edge count over the finite collection of drawable supergraphs containing the input graph; the size hypothesis is carried for the companion edge-count theorem.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_triangulating_supergraph_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
