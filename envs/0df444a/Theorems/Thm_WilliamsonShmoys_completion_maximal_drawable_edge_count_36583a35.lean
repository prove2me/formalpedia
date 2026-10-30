-- Prove2me | Theorems.Thm_WilliamsonShmoys_completion_maximal_drawable_edge_count_36583a35
-- name    : WilliamsonShmoys.completion_maximal_drawable_edge_count_36583a35
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:20:43.690208+00:00
-- url     : https://prove2.me/theorems/ebe94107-5d1b-45ae-ace1-61fa93ad502f
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable graph on at least three finite vertices that has no strictly larger drawable supergraph on those vertices has exactly `3|V|−6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.completion_maximal_drawable_edge_count_36583a35
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K)
    (hCard : 3 ≤ Fintype.card V) :
    (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
