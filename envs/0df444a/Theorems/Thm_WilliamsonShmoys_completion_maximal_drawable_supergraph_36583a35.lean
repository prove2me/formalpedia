-- Prove2me | Theorems.Thm_WilliamsonShmoys_completion_maximal_drawable_supergraph_36583a35
-- name    : WilliamsonShmoys.completion_maximal_drawable_supergraph_36583a35
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:13:38.553145+00:00
-- url     : https://prove2.me/theorems/7e29d976-ceba-4ffe-b18d-6619109a0118
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable supergraph maximal among drawable supergraphs on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.completion_maximal_drawable_supergraph_36583a35
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
