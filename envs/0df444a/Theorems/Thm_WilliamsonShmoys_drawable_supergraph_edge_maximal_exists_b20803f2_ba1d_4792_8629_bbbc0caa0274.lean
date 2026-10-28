-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_supergraph_edge_maximal_exists_b20803f2_ba1d_4792_8629_bbbc0caa0274
-- name    : WilliamsonShmoys.drawable_supergraph_edge_maximal_exists_b20803f2_ba1d_4792_8629_bbbc0caa0274
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:21:16.450198+00:00
-- url     : https://prove2.me/theorems/1722a9c1-65a1-4b94-96d7-0da187d99fcf
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable simple graph on a finite vertex type has a drawable supergraph that is maximal under edge inclusion among drawable graphs on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_supergraph_edge_maximal_exists_b20803f2_ba1d_4792_8629_bbbc0caa0274
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V, J.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
