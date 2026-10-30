-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawing_euler_bound_retry3
-- name    : WilliamsonShmoys.connected_drawing_euler_bound_retry3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:52:51.421655+00:00
-- url     : https://prove2.me/theorems/ab85cb2b-40de-4744-89cc-cdecc53b9a48
-- title:
--   Euler edge bound for a connected graph with a planar drawing
-- statement:
--   A finite connected simple graph on at least three vertices with a crossing-free drawing has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.connected_drawing_euler_bound_retry3 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hconn : G.Connected) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hcard : 3 <= Fintype.card V) : G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
