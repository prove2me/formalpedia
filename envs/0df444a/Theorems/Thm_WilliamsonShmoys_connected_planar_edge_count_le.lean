-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_le
-- name    : WilliamsonShmoys.connected_planar_edge_count_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:48:47.532035+00:00
-- url     : https://prove2.me/theorems/281837de-7879-4cff-aa77-87429d5e73ef
-- title:
--   Edge bound for a connected planar graph
-- statement:
--   A connected simple graph with a crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_count_le
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
