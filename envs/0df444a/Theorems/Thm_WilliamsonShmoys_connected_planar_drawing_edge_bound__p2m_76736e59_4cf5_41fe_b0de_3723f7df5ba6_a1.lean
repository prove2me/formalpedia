-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_bound__p2m_76736e59_4cf5_41fe_b0de_3723f7df5ba6_a1
-- name    : WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_76736e59_4cf5_41fe_b0de_3723f7df5ba6_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:52:08.071489+00:00
-- url     : https://prove2.me/theorems/5d599c83-54c6-426b-a50f-1d6092e7f607
-- title:
--   Edge bound for a connected finite planar drawing
-- statement:
--   A connected finite simple graph with the supplied planar drawing and at least three vertices has at most 3|V|−6 edges. This is the connected Euler-formula step: combine the Euler characteristic with the minimum length of a face boundary in a simple graph of this size.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_76736e59_4cf5_41fe_b0de_3723f7df5ba6_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hConn : H.Connected) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
