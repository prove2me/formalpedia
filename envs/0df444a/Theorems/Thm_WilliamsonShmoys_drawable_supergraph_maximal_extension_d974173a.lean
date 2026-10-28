-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_supergraph_maximal_extension_d974173a
-- name    : WilliamsonShmoys.drawable_supergraph_maximal_extension_d974173a
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:33:43.054503+00:00
-- url     : https://prove2.me/theorems/0fcbafe6-146a-40bd-b432-552841dedab5
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on that same vertex type that is maximal among drawable supergraphs containing it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.drawable_supergraph_maximal_extension_d974173a {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
