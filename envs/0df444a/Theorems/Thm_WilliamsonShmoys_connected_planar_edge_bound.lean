-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound
-- name    : WilliamsonShmoys.connected_planar_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T09:42:25.239996+00:00
-- url     : https://prove2.me/theorems/d4a948ef-ae31-4679-a96a-8f8ba13173ef
-- title:
--   Euler edge bound for connected planar graphs
-- statement:
--   A connected finite simple graph with the supplied plane drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hconn : L.Connected) (hV : 3 ≤ Fintype.card V) : L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
