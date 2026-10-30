-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_drawable_edge_bound
-- name    : WilliamsonShmoys.connected_drawable_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T12:09:01.27945+00:00
-- url     : https://prove2.me/theorems/b6739023-548b-4b2e-a781-9b00cc5e2c81
-- title:
--   Connected drawable simple graph edge bound
-- statement:
--   A finite connected simple graph with at least three vertices and a crossing-free drawing has at most three times its vertex count minus six edges. This is the Euler face-counting step: prove Euler’s relation for the drawing, show every face boundary has length at least three, and count edge sides across faces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_drawable_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
