-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bounds__p2m_997243ae_8756_4ede_bc08_017e56f3a3d3_a2
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_bounds__p2m_997243ae_8756_4ede_bc08_017e56f3a3d3_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T20:29:52.224753+00:00
-- url     : https://prove2.me/theorems/4d55918f-bbf7-4f10-a854-239f6af3f8f1
-- title:
--   Connected planar drawing edge bounds
-- statement:
--   A connected graph with a crossing-free drawing and at least three vertices has at least one fewer edge than vertices and at most three times the number of vertices minus six edges. The lower bound follows from a spanning tree; the upper bound is the simple planar graph edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

theorem WilliamsonShmoys.connected_planar_drawing_edge_bounds__p2m_997243ae_8756_4ede_bc08_017e56f3a3d3_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    Fintype.card V ≤ K.edgeSet.ncard + 1 ∧
      K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
