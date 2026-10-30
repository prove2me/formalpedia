-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_simple_graph_edge_bound_euler
-- name    : WilliamsonShmoys.connected_planar_simple_graph_edge_bound_euler
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:40:35.269123+00:00
-- url     : https://prove2.me/theorems/ad03280b-8932-45ec-892b-49e7cea65394
-- title:
--   Euler edge bound for connected planar simple graphs
-- statement:
--   A connected simple graph with the supplied planar drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_simple_graph_edge_bound_euler
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : ∀ u v, Relation.ReflTransGen G.Adj u v)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
