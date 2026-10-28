-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_graph_edge_count_v2_euler_face_witness
-- name    : WilliamsonShmoys.connected_planar_graph_edge_count_v2_euler_face_witness
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:12:58.194301+00:00
-- url     : https://prove2.me/theorems/32ec1d3c-0cf4-4dad-87f9-94cfd6d50484
-- title:
--   Euler face count for the connected planar drawing edge bound
-- statement:
--   A connected finite graph with the supplied crossing-free drawing has a natural-number face count satisfying Euler’s formula. The child isolates the drawing-to-Euler step; it does not require the lower bound on the number of vertices. A proof route is to form the plane embedding from the given arcs and apply Euler’s formula for connected plane graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_graph_edge_count_v2_euler_face_witness
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hconn : Y.Connected)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ f : ℕ, Fintype.card V + f = Y.edgeSet.ncard + 2 := by sorry
