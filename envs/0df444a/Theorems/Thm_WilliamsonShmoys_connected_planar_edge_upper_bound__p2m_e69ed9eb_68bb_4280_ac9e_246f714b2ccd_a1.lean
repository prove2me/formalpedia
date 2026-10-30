-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_upper_bound__p2m_e69ed9eb_68bb_4280_ac9e_246f714b2ccd_a1
-- name    : WilliamsonShmoys.connected_planar_edge_upper_bound__p2m_e69ed9eb_68bb_4280_ac9e_246f714b2ccd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T08:51:33.214777+00:00
-- url     : https://prove2.me/theorems/b29607d3-7938-4798-912f-c365f752475e
-- title:
--   Edge bound for connected planar graphs
-- statement:
--   A connected finite simple graph with the supplied crossing-free drawing and at least three vertices has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_upper_bound__p2m_e69ed9eb_68bb_4280_ac9e_246f714b2ccd_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hConn : G.Connected) (hCard : 3 ≤ Fintype.card V) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
