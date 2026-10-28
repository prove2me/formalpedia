-- Prove2me | Theorems.Thm_WilliamsonShmoys_ceaeb6d3_exists_inclusion_maximal_planar_supergraph_finite
-- name    : WilliamsonShmoys.ceaeb6d3_exists_inclusion_maximal_planar_supergraph_finite
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:24:16.063205+00:00
-- url     : https://prove2.me/theorems/dde77454-22b4-420b-8fa8-f9347f460581
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph that is maximal under edge inclusion among drawable supergraphs on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.ceaeb6d3_exists_inclusion_maximal_planar_supergraph_finite
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet ⊆ H.edgeSet) := by sorry
