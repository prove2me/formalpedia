-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound
-- name    : WilliamsonShmoys.connected_planar_edge_count_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:43:17.410472+00:00
-- url     : https://prove2.me/theorems/d53792eb-424a-4aee-892a-ee6973ad808e
-- title:
--   Euler edge bound for connected planar graphs
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices satisfies the planar Euler edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_count_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hCard : 3 ≤ Fintype.card V)
    (hconn : X.Connected) :
    X.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
