-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_triangulated_supergraph_v10
-- name    : WilliamsonShmoys.drawable_triangulated_supergraph_v10
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:12:06.895894+00:00
-- url     : https://prove2.me/theorems/795238c0-700c-46b8-8fab-e92e18a7e391
-- title:
--   A drawable graph extends to a triangulated drawable graph
-- statement:
--   Every graph with the specified crossing-free drawing on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_triangulated_supergraph_v10 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 <= Fintype.card V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) : Exists fun M : SimpleGraph V => L <= M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
