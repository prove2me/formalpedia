-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_count_euler_bound
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_count_euler_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:52:57.939993+00:00
-- url     : https://prove2.me/theorems/28f71b70-f478-4fc7-9229-e048bdc66d13
-- title:
--   Euler edge bound for a connected finite simple planar drawing
-- statement:
--   A connected finite simple graph on at least three vertices with the supplied crossing-free drawing has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

theorem WilliamsonShmoys.connected_planar_drawing_edge_count_euler_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : Y.Connected)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    Y.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
