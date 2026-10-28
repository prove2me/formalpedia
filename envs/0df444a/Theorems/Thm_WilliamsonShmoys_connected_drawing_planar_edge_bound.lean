-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawing_planar_edge_bound
-- name    : WilliamsonShmoys.connected_drawing_planar_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T21:53:15.489262+00:00
-- url     : https://prove2.me/theorems/d9d46aa9-2bf0-442c-a352-ab7229a25dd7
-- title:
--   Simple planar edge bound from a connected drawing
-- statement:
--   A finite connected simple graph with at least three vertices and the supplied crossing-free drawing has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.connected_drawing_planar_edge_bound {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hconn : G.Connected) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
