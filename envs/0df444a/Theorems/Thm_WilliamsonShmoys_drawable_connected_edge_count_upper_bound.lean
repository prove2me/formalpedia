-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawable_connected_edge_count_upper_bound
-- name    : WilliamsonShmoys.drawable_connected_edge_count_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:58:38.787973+00:00
-- url     : https://prove2.me/theorems/9b7dc0d6-58f7-46d1-89ca-75df75c378f2
-- title:
--   Connected drawable simple graphs satisfy the planar edge bound
-- statement:
--   A connected drawable simple graph on at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.drawable_connected_edge_count_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConn : W.Connected)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    W.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
