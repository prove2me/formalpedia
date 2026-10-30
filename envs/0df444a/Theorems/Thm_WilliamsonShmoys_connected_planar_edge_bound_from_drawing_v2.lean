-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_from_drawing_v2
-- name    : WilliamsonShmoys.connected_planar_edge_bound_from_drawing_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T02:47:23.160125+00:00
-- url     : https://prove2.me/theorems/8fef8933-f1ab-42eb-9f94-324226ad43f5
-- title:
--   Edge bound for a connected graph with a planar drawing
-- statement:
--   A connected finite simple graph with at least three vertices and the specified crossing-free drawing has at most 3|V| - 6 edges. The proof can turn the drawing into a plane embedding, extend it to a maximal simple planar graph on the same vertices, and use Euler’s formula and triangular face counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound_from_drawing_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hConn : G.Connected)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
