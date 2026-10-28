-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_c00979a8
-- name    : WilliamsonShmoys.connected_planar_edge_bound_c00979a8
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T00:27:26.831861+00:00
-- url     : https://prove2.me/theorems/7ddee9d8-107a-4821-9b0c-d1281ad460b5
-- title:
--   Edge bound for a connected planar drawing
-- statement:
--   A connected finite simple graph on at least three vertices with the specified crossing-free drawing has at most three times its number of vertices minus six edges, by planar Euler counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.connected_planar_edge_bound_c00979a8 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 <= Fintype.card V) (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
