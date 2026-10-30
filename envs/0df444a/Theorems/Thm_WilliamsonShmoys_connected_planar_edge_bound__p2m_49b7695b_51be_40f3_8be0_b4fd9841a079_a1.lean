-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_49b7695b_51be_40f3_8be0_b4fd9841a079_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_49b7695b_51be_40f3_8be0_b4fd9841a079_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:21:00.713019+00:00
-- url     : https://prove2.me/theorems/ed9a163f-a427-4bb6-adf9-73a7e049aa03
-- title:
--   Connected planar graph edge bound
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most three times its number of vertices minus six edges. This isolates the geometric planar edge-count argument from the target’s subgraph transfer.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_49b7695b_51be_40f3_8be0_b4fd9841a079_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hconn : G.Connected)
    (hplanar : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
