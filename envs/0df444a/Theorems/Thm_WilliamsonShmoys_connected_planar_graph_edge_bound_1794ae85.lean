-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_graph_edge_bound_1794ae85
-- name    : WilliamsonShmoys.connected_planar_graph_edge_bound_1794ae85
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:24:28.372325+00:00
-- url     : https://prove2.me/theorems/beed4c34-fba2-4c7a-ab44-510e1be87d25
-- title:
--   Edge bound for connected drawable graphs
-- statement:
--   A connected drawable simple graph on at least three vertices has at most three times its vertex count minus six edges. This isolates the Euler-formula edge-count argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_graph_edge_bound_1794ae85
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
