-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound_euler_20261028
-- name    : WilliamsonShmoys.connected_planar_edge_count_bound_euler_20261028
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T22:15:19.437977+00:00
-- url     : https://prove2.me/theorems/2d5919db-2703-47fe-a41e-9dd279391179
-- title:
--   Euler edge bound for a connected planar drawing
-- statement:
--   A connected simple graph on at least three vertices with a drawing satisfying `HasPlanarDrawingOn` has at most `3 * Fintype.card V - 6` edges. A proof route is Euler's formula together with the lower bound on face boundary lengths for a simple graph of this size.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_count_bound_euler_20261028
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : G.Connected)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
