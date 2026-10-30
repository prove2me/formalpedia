-- Prove2me | Theorems.Thm_WilliamsonShmoys_dense_of_maximal_drawable__p2m_6630bfc0_6fd3_4ee5_a018_4b73345ede9f_a2
-- name    : WilliamsonShmoys.dense_of_maximal_drawable__p2m_6630bfc0_6fd3_4ee5_a018_4b73345ede9f_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:43:23.230106+00:00
-- url     : https://prove2.me/theorems/6f64e769-ed8d-4f23-84ce-0685c66257bc
-- title:
--   Density of a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph has at least `3|V| − 6` edges. The size hypothesis covers the small boundary case; for three vertices the bound is three edges. A proof route is to show maximality forces a connected triangulation, then apply Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.dense_of_maximal_drawable__p2m_6630bfc0_6fd3_4ee5_a018_4b73345ede9f_a2 {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q) (hMax : ∀ R : SimpleGraph V, Q ≤ R → HasPlanarDrawingOn R → R ≤ Q) (hV : 3 ≤ Fintype.card V) : 3 * Fintype.card V ≤ Q.edgeSet.ncard + 6 := by sorry
