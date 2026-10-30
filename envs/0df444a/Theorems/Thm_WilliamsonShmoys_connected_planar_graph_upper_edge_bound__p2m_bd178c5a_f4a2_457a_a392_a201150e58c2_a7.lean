-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_graph_upper_edge_bound__p2m_bd178c5a_f4a2_457a_a392_a201150e58c2_a7
-- name    : WilliamsonShmoys.connected_planar_graph_upper_edge_bound__p2m_bd178c5a_f4a2_457a_a392_a201150e58c2_a7
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T09:25:37.363992+00:00
-- url     : https://prove2.me/theorems/07412642-07f6-4c9a-bcad-c9e213df7ef1
-- title:
--   Edge bound for connected planar simple graphs
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges. Extract a finite plane embedding, apply Euler’s formula, then count face-boundary incidences; augmentation handles bridges and faces of degree below three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.connected_planar_graph_upper_edge_bound__p2m_bd178c5a_f4a2_457a_a392_a201150e58c2_a7
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hconn : L.Connected)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
