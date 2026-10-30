-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_39b19b3a_0192_4155_8e70_5ad145d3ea40_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_39b19b3a_0192_4155_8e70_5ad145d3ea40_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T09:31:59.320968+00:00
-- url     : https://prove2.me/theorems/f77c312c-ffe6-4764-83df-1234c221d04d
-- title:
--   Edge bound for a connected drawn graph
-- statement:
--   A finite simple graph on at least three vertices with a crossing-free drawing and connected underlying graph has at most three times its number of vertices minus six edges. This is the Euler-formula step; it handles the smallest allowed order as well.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_39b19b3a_0192_4155_8e70_5ad145d3ea40_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hConn : G.Connected)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
