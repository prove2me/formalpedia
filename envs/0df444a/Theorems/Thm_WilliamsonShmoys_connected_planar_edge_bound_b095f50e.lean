-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_b095f50e
-- name    : WilliamsonShmoys.connected_planar_edge_bound_b095f50e
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T21:54:10.409996+00:00
-- url     : https://prove2.me/theorems/32347207-f4f9-43c0-a956-7b54196e9b00
-- title:
--   Edge bound for a connected graph with a planar drawing
-- statement:
--   A connected finite simple graph on at least three vertices with the supplied crossing-free drawing has at most three times its vertex count minus six edges. The source-backed route is to pass from the drawing to a spherical embedding, apply Euler’s formula, and count at least three edge incidences per face. The size hypothesis excludes the small connected graphs where this bound does not hold. Formalizing that topological route is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

theorem WilliamsonShmoys.connected_planar_edge_bound_b095f50e
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : G.Connected)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
