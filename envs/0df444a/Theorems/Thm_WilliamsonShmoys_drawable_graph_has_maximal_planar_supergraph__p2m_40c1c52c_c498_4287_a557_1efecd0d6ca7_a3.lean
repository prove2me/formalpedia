-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_graph_has_maximal_planar_supergraph__p2m_40c1c52c_c498_4287_a557_1efecd0d6ca7_a3
-- name    : WilliamsonShmoys.drawable_graph_has_maximal_planar_supergraph__p2m_40c1c52c_c498_4287_a557_1efecd0d6ca7_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:20:19.765382+00:00
-- url     : https://prove2.me/theorems/f3863ecb-d96f-4f01-8e13-caf8f4700d63
-- title:
--   Finite maximal drawable supergraph exists
-- statement:
--   Any drawable graph on a finite vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_graph_has_maximal_planar_supergraph__p2m_40c1c52c_c498_4287_a557_1efecd0d6ca7_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by
  sorry
