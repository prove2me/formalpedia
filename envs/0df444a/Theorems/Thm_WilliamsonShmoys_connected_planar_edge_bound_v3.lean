-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_v3
-- name    : WilliamsonShmoys.connected_planar_edge_bound_v3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:47:05.65999+00:00
-- url     : https://prove2.me/theorems/08e924b6-7f1f-4090-af65-8c7d133a96f4
-- title:
--   Edge bound for a connected planar drawing
-- statement:
--   A connected simple graph on at least three vertices with the packaged crossing-free drawing has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound_v3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hConn : H.Connected) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
