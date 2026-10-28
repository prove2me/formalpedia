-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound_from_drawing
-- name    : WilliamsonShmoys.connected_planar_edge_count_bound_from_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T21:48:31.601094+00:00
-- url     : https://prove2.me/theorems/85e592f4-6f57-4d69-8bbf-933570e3c9fe
-- title:
--   Planar edge bound for connected graphs from a drawing
-- statement:
--   A connected simple graph with a crossing-free drawing on at least three vertices has at most three times its vertex count minus six edges. The size hypothesis excludes the small connected graphs where the usual face-boundary argument needs separate treatment.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_count_bound_from_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConnected : G.Connected)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
