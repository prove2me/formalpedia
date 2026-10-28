-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_upper_bound_for_component_edge_bound
-- name    : WilliamsonShmoys.connected_planar_edge_count_upper_bound_for_component_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T09:57:12.697908+00:00
-- url     : https://prove2.me/theorems/a90184ce-ee9b-446c-ba5f-8b914323af6c
-- title:
--   Edge bound for a connected planar graph
-- statement:
--   A finite connected simple graph with a planar drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_count_upper_bound_for_component_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hconn : G.Connected) :
    3 ≤ Fintype.card V → G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
