-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_edge_count_le_three_n_sub_six_from_drawing__p2m_5438d717_60ba_4719_bd8d_a39b0e45c967_a4
-- name    : WilliamsonShmoys.connected_edge_count_le_three_n_sub_six_from_drawing__p2m_5438d717_60ba_4719_bd8d_a39b0e45c967_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T05:03:11.756999+00:00
-- url     : https://prove2.me/theorems/65cf0999-c5b2-4971-827b-e0cd6da5e0b2
-- title:
--   Connected planar Euler edge bound
-- statement:
--   A connected finite simple graph with the supplied planar drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_edge_count_le_three_n_sub_six_from_drawing__p2m_5438d717_60ba_4719_bd8d_a39b0e45c967_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hConnected : N.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    N.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
