-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_09553c75_05d3_4866_a115_40c42a94c393_a2
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_09553c75_05d3_4866_a115_40c42a94c393_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:55:10.582991+00:00
-- url     : https://prove2.me/theorems/1aa142c3-2879-49d1-9ded-02a2d2269a9c
-- title:
--   Euler edge bound for a connected finite planar drawing
-- statement:
--   A connected finite simple graph with at least three vertices and the specified planar drawing satisfies the Euler edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_09553c75_05d3_4866_a115_40c42a94c393_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
