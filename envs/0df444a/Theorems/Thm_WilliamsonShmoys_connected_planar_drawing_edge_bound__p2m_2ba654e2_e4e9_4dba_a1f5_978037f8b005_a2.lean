-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound__p2m_2ba654e2_e4e9_4dba_a1f5_978037f8b005_a2
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_2ba654e2_e4e9_4dba_a1f5_978037f8b005_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:52:47.291001+00:00
-- url     : https://prove2.me/theorems/e5510062-79cf-414b-9e60-87983ccc5318
-- title:
--   Edge bound for a connected planar drawing
-- statement:
--   A connected simple graph with the specified crossing-free drawing and at least three vertices has at most 3n−6 edges. Prove this by separating the tree case, then counting face incidences and applying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_2ba654e2_e4e9_4dba_a1f5_978037f8b005_a2 {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hDraw : HasPlanarDrawingOn S) (hConnected : S.Connected) (hV : 3 <= Fintype.card V) : S.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
