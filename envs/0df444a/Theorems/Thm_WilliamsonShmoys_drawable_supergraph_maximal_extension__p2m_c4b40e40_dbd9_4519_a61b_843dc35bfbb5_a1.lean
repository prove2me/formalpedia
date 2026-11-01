-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_supergraph_maximal_extension__p2m_c4b40e40_dbd9_4519_a61b_843dc35bfbb5_a1
-- name    : WilliamsonShmoys.drawable_supergraph_maximal_extension__p2m_c4b40e40_dbd9_4519_a61b_843dc35bfbb5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:45:47.264714+00:00
-- url     : https://prove2.me/theorems/6008d3c0-4478-43cb-bb9c-49ec0c6affa9
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_supergraph_maximal_extension__p2m_c4b40e40_dbd9_4519_a61b_843dc35bfbb5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, M ≤ N →
          WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by sorry
