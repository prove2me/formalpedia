-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T02:57:31.095007+00:00
-- url     : https://prove2.me/theorems/e5cffa02-fe32-4514-8b5f-3ae37ad87963
-- title:
--   Euler edge bound for connected planar drawings
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  sorry
