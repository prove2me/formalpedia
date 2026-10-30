-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_completion__p2m_9329bbd1_6fa9_431d_b5f3_646d0c97c054_a2
-- name    : WilliamsonShmoys.drawable_graph_has_maximal_completion__p2m_9329bbd1_6fa9_431d_b5f3_646d0c97c054_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:42:17.839799+00:00
-- url     : https://prove2.me/theorems/17bd3fa2-c9c6-4c63-b04a-aaecb94be96d
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Among drawable supergraphs of K on the finite vertex type V, there is one containing every other drawable supergraph of K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_maximal_completion__p2m_9329bbd1_6fa9_431d_b5f3_646d0c97c054_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V, K ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ M := by sorry
