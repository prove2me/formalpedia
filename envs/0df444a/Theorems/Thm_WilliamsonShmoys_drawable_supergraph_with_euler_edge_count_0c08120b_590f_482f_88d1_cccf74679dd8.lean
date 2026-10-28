-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_supergraph_with_euler_edge_count_0c08120b_590f_482f_88d1_cccf74679dd8
-- name    : WilliamsonShmoys.drawable_supergraph_with_euler_edge_count_0c08120b_590f_482f_88d1_cccf74679dd8
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T13:15:04.060335+00:00
-- url     : https://prove2.me/theorems/87a22553-dea2-4f4b-84fd-2bea87c50680
-- title:
--   Drawable supergraph with the planar Euler edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges, containing all original edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.drawable_supergraph_with_euler_edge_count_0c08120b_590f_482f_88d1_cccf74679dd8 {V : Type} [Fintype V] [LinearOrder V] (X : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn X) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, X ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ X.edgeSet.ncard ≤ H.edgeSet.ncard ∧ H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
