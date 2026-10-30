-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound_v2
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_bound_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:31:11.275063+00:00
-- url     : https://prove2.me/theorems/77ed1e70-1730-4949-95d2-891dbf444f88
-- title:
--   Euler edge bound for connected planar drawings
-- statement:
--   A connected finite simple graph with at least three vertices and a planar drawing has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.connected_planar_drawing_edge_bound_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  sorry
