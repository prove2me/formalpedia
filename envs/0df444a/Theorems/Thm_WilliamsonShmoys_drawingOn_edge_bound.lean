-- Prove2me | Theorems.Thm_WilliamsonShmoys_drawingOn_edge_bound
-- name    : WilliamsonShmoys.drawingOn_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:10:22.006373+00:00
-- url     : https://prove2.me/theorems/2176aa89-35ce-4f3e-87b9-1edffd813bba
-- title:
--   Simple planar graph edge bound
-- statement:
--   A connected simple graph with at least three vertices and the supplied planar drawing has at most 3n − 6 edges, stated without truncated natural subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.drawingOn_edge_bound {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hconn : G.Connected) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
