-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_simple_graph_edge_card_upper_bound__p2m_01732aef_dd3e_4b78_a11c_771f0411d541_a1
-- name    : WilliamsonShmoys.connected_planar_simple_graph_edge_card_upper_bound__p2m_01732aef_dd3e_4b78_a11c_771f0411d541_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:58:46.542712+00:00
-- url     : https://prove2.me/theorems/26b20229-4922-4282-8d13-2bf152659d7b
-- title:
--   Edge bound for a connected drawable simple graph
-- statement:
--   A connected drawable finite simple graph with at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_simple_graph_edge_card_upper_bound__p2m_01732aef_dd3e_4b78_a11c_771f0411d541_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      K.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
