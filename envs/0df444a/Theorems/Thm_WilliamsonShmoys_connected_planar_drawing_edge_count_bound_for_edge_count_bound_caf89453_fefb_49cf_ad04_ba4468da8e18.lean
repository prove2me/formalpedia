-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_count_bound_for_edge_count_bound_caf89453_fefb_49cf_ad04_ba4468da8e18
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_count_bound_for_edge_count_bound_caf89453_fefb_49cf_ad04_ba4468da8e18
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:33:40.204979+00:00
-- url     : https://prove2.me/theorems/10124dd3-3690-461c-9ae9-0d3a5e62ad84
-- title:
--   Edge bound for a connected planar drawing
-- statement:
--   A connected finite simple graph with at least three vertices and the specified crossing-free drawing has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_edge_count_bound_for_edge_count_bound_caf89453_fefb_49cf_ad04_ba4468da8e18 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hConn : G.Connected) (hCard : 3 ≤ Fintype.card V) : G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
