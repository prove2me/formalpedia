-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_graph_edge_bound__p2m_e0c85ed3_29c9_4753_86a9_a6c3e4be15ff_a2
-- name    : WilliamsonShmoys.connected_planar_graph_edge_bound__p2m_e0c85ed3_29c9_4753_86a9_a6c3e4be15ff_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:53:28.629202+00:00
-- url     : https://prove2.me/theorems/02efd696-96fe-4670-9021-ba912a848fde
-- title:
--   Euler edge bound for connected planar simple graphs
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_graph_edge_bound__p2m_e0c85ed3_29c9_4753_86a9_a6c3e4be15ff_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : G.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj
     G.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
