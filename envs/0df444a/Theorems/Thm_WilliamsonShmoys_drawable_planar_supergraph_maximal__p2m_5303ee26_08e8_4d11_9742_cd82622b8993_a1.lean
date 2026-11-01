-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_planar_supergraph_maximal__p2m_5303ee26_08e8_4d11_9742_cd82622b8993_a1
-- name    : WilliamsonShmoys.drawable_planar_supergraph_maximal__p2m_5303ee26_08e8_4d11_9742_cd82622b8993_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:35:50.528732+00:00
-- url     : https://prove2.me/theorems/19fdcf06-1b97-4a80-a594-889b4795843b
-- title:
--   Every drawable graph has a maximal drawable supergraph
-- statement:
--   Any drawable graph on a finite vertex type with at least three vertices has an inclusion-maximal drawable supergraph on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.drawable_planar_supergraph_maximal__p2m_5303ee26_08e8_4d11_9742_cd82622b8993_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ HasPlanarDrawingOn N ∧
        ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N := by
  sorry
