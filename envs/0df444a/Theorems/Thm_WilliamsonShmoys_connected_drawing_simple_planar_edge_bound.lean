-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawing_simple_planar_edge_bound
-- name    : WilliamsonShmoys.connected_drawing_simple_planar_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T09:40:28.660736+00:00
-- url     : https://prove2.me/theorems/2946c9d9-e9a3-47ed-8c98-566169fce89e
-- title:
--   Simple planar edge bound from a connected drawing
-- statement:
--   A finite simple graph on at least three vertices with the supplied connected planar drawing has at most 3n − 6 edges, expressed without natural-number subtraction as m + 6 ≤ 3n.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_drawing_simple_planar_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
