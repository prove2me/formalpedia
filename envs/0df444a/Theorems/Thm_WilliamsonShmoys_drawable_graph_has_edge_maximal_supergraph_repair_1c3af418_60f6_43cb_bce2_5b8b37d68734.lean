-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_edge_maximal_supergraph_repair_1c3af418_60f6_43cb_bce2_5b8b37d68734
-- name    : WilliamsonShmoys.drawable_graph_has_edge_maximal_supergraph_repair_1c3af418_60f6_43cb_bce2_5b8b37d68734
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T07:23:05.31998+00:00
-- url     : https://prove2.me/theorems/9322a59b-2170-4744-ada3-ba2eeb4e5031
-- title:
--   Extend a drawable graph to an edge-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on the same vertices that is maximal under edge inclusion. The proof can choose a maximal element among the finitely many drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_graph_has_edge_maximal_supergraph_repair_1c3af418_60f6_43cb_bce2_5b8b37d68734
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeSet ⊆ N.edgeSet ∧
      (∀ P : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn P →
        N.edgeSet ⊆ P.edgeSet → P.edgeSet = N.edgeSet) := by sorry
