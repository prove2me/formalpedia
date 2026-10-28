-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_upper_bound
-- name    : WilliamsonShmoys.connected_planar_edge_upper_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:08:48.740897+00:00
-- url     : https://prove2.me/theorems/44582a15-9e97-4400-a904-211b2bb40660
-- title:
--   Edge bound for connected planar drawings
-- statement:
--   Every connected finite simple graph with the specified planar drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
