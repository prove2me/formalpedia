-- Prove2me | Theorems.Thm_WilliamsonShmoys_card_eq_three_n_sub_six_of_planar_maximal
-- name    : WilliamsonShmoys.card_eq_three_n_sub_six_of_planar_maximal
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T22:12:21.461188+00:00
-- url     : https://prove2.me/theorems/3283e70a-bf65-40e4-a209-7c126eda83bf
-- title:
--   An edge-maximal finite planar drawing has 3n minus 6 edges
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on those vertices has exactly 3n minus 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.card_eq_three_n_sub_six_of_planar_maximal
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
