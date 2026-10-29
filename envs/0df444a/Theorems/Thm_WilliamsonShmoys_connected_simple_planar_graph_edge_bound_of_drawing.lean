-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_simple_planar_graph_edge_bound_of_drawing
-- name    : WilliamsonShmoys.connected_simple_planar_graph_edge_bound_of_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:11:41.070212+00:00
-- url     : https://prove2.me/theorems/8b78ce70-f4db-4efb-b7ef-3fe031695572
-- title:
--   Edge bound for a connected simple planar graph drawing
-- statement:
--   A connected simple graph with at least three vertices and a crossing-free drawing has at most three times its number of vertices minus six edges, expressed without natural subtraction as m + 6 ≤ 3n.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_simple_planar_graph_edge_bound_of_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : L.Connected)
    (hdraw : HasPlanarDrawingOn L) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
