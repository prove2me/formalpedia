-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_graph_edge_count_v2
-- name    : WilliamsonShmoys.connected_planar_graph_edge_count_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:49:57.932263+00:00
-- url     : https://prove2.me/theorems/257dd07d-728e-4f51-9000-a9b580e580a0
-- title:
--   Edge bound for connected graphs with a planar drawing
-- statement:
--   A connected finite graph with at least three vertices and a crossing-free drawing has at most 3|V| − 6 edges. This isolates the Euler formula and face-incidence argument from the disconnected case. One proof route is to establish Euler's formula for the drawing, count edge incidences around faces, and show that at least three incidences per face are required under the stated hypotheses.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_graph_edge_count_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : Y.Connected)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    Y.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
