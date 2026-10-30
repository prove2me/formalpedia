-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound_via_euler
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_bound_via_euler
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:32:42.429392+00:00
-- url     : https://prove2.me/theorems/f59531a3-45b4-49d8-8738-5cd4e06ffb26
-- title:
--   Connected planar drawing edge bound from Euler’s formula
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_edge_bound_via_euler {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hdraw : HasPlanarDrawingOn G) (hconn : G.Connected) (hV : 3 <= Fintype.card V) : G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
