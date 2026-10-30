-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawable_edge_bound_3daf7e3a
-- name    : WilliamsonShmoys.connected_drawable_edge_bound_3daf7e3a
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:25:13.203112+00:00
-- url     : https://prove2.me/theorems/6a8d1e34-1b9f-4372-8a14-b5efc6adec09
-- title:
--   Euler edge bound for connected drawable graphs
-- statement:
--   A connected drawable finite simple graph with at least three vertices satisfies the Euler edge bound. The drawing and connectedness hypotheses are both needed for the proposed face-count argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_drawable_edge_bound_3daf7e3a
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hPconn : P.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    P.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
