-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawing_edge_bound_large_e9dfd49a
-- name    : WilliamsonShmoys.connected_drawing_edge_bound_large_e9dfd49a
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T04:14:12.060892+00:00
-- url     : https://prove2.me/theorems/e1c8b881-67e0-4b9f-ab35-1c2d56e4195d
-- title:
--   Edge bound for a connected planar drawing
-- statement:
--   A connected finite simple graph with the supplied crossing-free drawing and at least three vertices has at most 3|V|−6 edges, by Euler’s formula and face-boundary counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.connected_drawing_edge_bound_large_e9dfd49a
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConnected : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    (G.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 := by sorry
