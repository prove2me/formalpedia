-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound_core_4db24ad1
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_bound_core_4db24ad1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:49:28.140008+00:00
-- url     : https://prove2.me/theorems/669cfd2c-d4b3-40ab-895b-2ab8080fff5c
-- title:
--   Connected planar edge bound from a drawing
-- statement:
--   A connected simple graph with at least three vertices and a crossing-free drawing has at most 3n − 6 edges. This is the topological core of the reduction. A proof route is to establish Euler’s relation for the given drawing using Jordan separation and derive the simple planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_edge_bound_core_4db24ad1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : L.Connected)
    (hdraw : HasPlanarDrawingOn L) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
