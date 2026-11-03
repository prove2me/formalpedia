-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_7e43e1d3_8cc5_4078_adc3_512d6b4c19e6_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_7e43e1d3_8cc5_4078_adc3_512d6b4c19e6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:33:29.365538+00:00
-- url     : https://prove2.me/theorems/1ec71208-cc1c-45fa-ad3a-a9c7012c7f6f
-- title:
--   Simple planar graph edge bound
-- statement:
--   A simple connected planar graph with at least three vertices has at most 3V − 6 edges, expressed without truncated natural subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_7e43e1d3_8cc5_4078_adc3_512d6b4c19e6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hconn : N.Connected) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     N.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
