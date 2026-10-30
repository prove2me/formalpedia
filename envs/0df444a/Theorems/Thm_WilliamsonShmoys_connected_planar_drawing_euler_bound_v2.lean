-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_euler_bound_v2
-- name    : WilliamsonShmoys.connected_planar_drawing_euler_bound_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:54:52.234728+00:00
-- url     : https://prove2.me/theorems/7190fb2e-778b-40a3-8644-b8c9eec0e75d
-- title:
--   Euler edge bound for connected simple planar drawings
-- statement:
--   A finite connected simple graph with at least three vertices and a crossing-free drawing has at most three times its vertex count minus six edges. This is the Euler counting step used after connecting the drawing’s components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_euler_bound_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L)
    (hConnected : L.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
