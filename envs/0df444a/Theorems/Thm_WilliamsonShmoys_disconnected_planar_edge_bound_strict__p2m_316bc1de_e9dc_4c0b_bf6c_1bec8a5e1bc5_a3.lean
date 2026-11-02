-- Prove2me | Theorems.Thm_WilliamsonShmoys_disconnected_planar_edge_bound_strict__p2m_316bc1de_e9dc_4c0b_bf6c_1bec8a5e1bc5_a3
-- name    : WilliamsonShmoys.disconnected_planar_edge_bound_strict__p2m_316bc1de_e9dc_4c0b_bf6c_1bec8a5e1bc5_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:00:42.690206+00:00
-- url     : https://prove2.me/theorems/b828f8d7-ba0b-4b6d-9733-7bef5e5f95bb
-- title:
--   Strict planar edge bound for disconnected drawings
-- statement:
--   A disconnected finite simple graph with a crossing-free drawing and at least three vertices has at least one edge less than the general planar upper bound: its edge count plus seven is at most three times its vertex count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_093d3833_026f_4cc9_9066_8ef7487e85b6_a2
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.disconnected_planar_edge_bound_strict__p2m_316bc1de_e9dc_4c0b_bf6c_1bec8a5e1bc5_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) (hconn : ¬ M.Connected) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj;
     M.edgeFinset.card + 7 ≤ 3 * Fintype.card V) := by sorry
