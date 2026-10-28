-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_a8cccb55
-- name    : WilliamsonShmoys.connected_planar_edge_bound_a8cccb55
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T09:20:14.570121+00:00
-- url     : https://prove2.me/theorems/c4ce6f4e-74ea-4a01-bfad-3bdb7ed8f51d
-- title:
--   Edge bound for a connected drawn simple graph
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound_a8cccb55
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : W.Connected)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    W.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
