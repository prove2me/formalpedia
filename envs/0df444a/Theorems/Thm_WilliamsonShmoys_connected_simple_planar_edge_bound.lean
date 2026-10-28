-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_simple_planar_edge_bound
-- name    : WilliamsonShmoys.connected_simple_planar_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T16:11:05.092984+00:00
-- url     : https://prove2.me/theorems/005e9bf4-ca96-4c80-9e24-c1c11b9d52d3
-- title:
--   Edge bound for connected simple planar drawings
-- statement:
--   A finite connected simple graph with at least three vertices and a `HasPlanarDrawingOn` drawing has at most 3|V| − 6 edges, expressed without truncated subtraction as |E| + 6 ≤ 3|V|. This includes trees and the equality boundary at a triangulated planar graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_simple_planar_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
