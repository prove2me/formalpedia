-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_graph_edge_count
-- name    : WilliamsonShmoys.connected_planar_graph_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:53:15.194816+00:00
-- url     : https://prove2.me/theorems/76e2838c-6ef9-4c97-9d0c-a794548a3824
-- title:
--   Edge bound for connected graphs with a planar drawing
-- statement:
--   A connected finite graph with at least three vertices and a crossing-free drawing has at most 3|V|−6 edges. This isolates the Euler formula and face-incidence counting argument; an independent route is to prove Euler’s formula for the given drawing and show every face contributes at least three edge incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_graph_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : Y.Connected)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    Y.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
