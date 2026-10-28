-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_completion_from_augmentation
-- name    : WilliamsonShmoys.drawable_completion_from_augmentation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:36:32.673667+00:00
-- url     : https://prove2.me/theorems/4b286cc7-ce24-42ee-876e-bbf797130941
-- title:
--   Complete a drawable graph by finite augmentation
-- statement:
--   Given a drawable starting graph, a uniform edge-count upper bound, and one-edge drawable augmentation below the bound for every drawable supergraph of the start, finite induction reaches the bound exactly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_completion_from_augmentation
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hBound : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet.ncard ≤ 3 * Fintype.card V - 6)
    (hAug : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet.ncard < 3 * Fintype.card V - 6 →
      ∃ N : SimpleGraph V,
        M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        N.edgeSet.ncard = M.edgeSet.ncard + 1) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V - 6 = M.edgeSet.ncard := by
  sorry
