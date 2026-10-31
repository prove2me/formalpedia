-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound__p2m_b17d3809_e307_4597_82b6_1d4f1ebd7e38_a1
-- name    : WilliamsonShmoys.connected_planar_edge_bound__p2m_b17d3809_e307_4597_82b6_1d4f1ebd7e38_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T08:45:34.723483+00:00
-- url     : https://prove2.me/theorems/ceffe8f7-0bd7-41ea-898f-3fe9bc8f26e2
-- title:
--   Connected planar edge count bound
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound__p2m_b17d3809_e307_4597_82b6_1d4f1ebd7e38_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hConn : P.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    P.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
