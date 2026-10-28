-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_triangulation_supergraph_choose_max_v2
-- name    : WilliamsonShmoys.drawable_triangulation_supergraph_choose_max_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:25:15.195111+00:00
-- url     : https://prove2.me/theorems/b53317b8-1e8d-4dac-ad06-a7c65cef0061
-- title:
--   Choose a drawable supergraph with maximum edge count
-- statement:
--   Among the drawable supergraphs of a finite drawable graph on the same vertex type, one has maximum edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_triangulation_supergraph_choose_max_v2 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hdraw : HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ ∀ M : SimpleGraph V, K ≤ M → HasPlanarDrawingOn M → M.edgeSet.ncard ≤ L.edgeSet.ncard := by sorry
