-- Prove2me | Theorems.Thm_WilliamsonShmoys_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_2a9c79db_1ecc_4cf4_ab9e_7f8c5fd1a388_a5
-- name    : WilliamsonShmoys.WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_2a9c79db_1ecc_4cf4_ab9e_7f8c5fd1a388_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:14:41.801835+00:00
-- url     : https://prove2.me/theorems/2ea99569-5736-493f-8895-a821efa27469
-- title:
--   Maximal drawable graph edge lower bound
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has at least 3|V|−6 edges. This removes the saturation and lower-bound argument from the parent. A proof route is to use maximality to show the drawing is connected and every face is triangular, then combine Euler’s formula with face-edge incidence counting. At three vertices maximality gives the triangle, so the boundary case satisfies the stated bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_2a9c79db_1ecc_4cf4_ab9e_7f8c5fd1a388_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : HasPlanarDrawingOn G)
    (hmax : forall R : SimpleGraph V, G <= R -> HasPlanarDrawingOn R -> R <= G) :
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    3 * Fintype.card V <= G.edgeFinset.card + 6 := by sorry
