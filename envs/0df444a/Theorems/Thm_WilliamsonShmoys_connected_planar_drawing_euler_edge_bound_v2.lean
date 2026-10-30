-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_edge_bound_v2
-- name    : WilliamsonShmoys.connected_planar_drawing_euler_edge_bound_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:33:08.3141+00:00
-- url     : https://prove2.me/theorems/53e27366-5057-47bc-bf2d-b4217413896d
-- title:
--   Euler edge bound for connected planar drawings
-- statement:
--   A connected simple planar graph with at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_drawing_euler_edge_bound_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
