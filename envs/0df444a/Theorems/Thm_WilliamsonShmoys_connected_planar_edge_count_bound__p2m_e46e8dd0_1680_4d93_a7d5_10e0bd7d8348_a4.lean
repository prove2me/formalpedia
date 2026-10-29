-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound__p2m_e46e8dd0_1680_4d93_a7d5_10e0bd7d8348_a4
-- name    : WilliamsonShmoys.connected_planar_edge_count_bound__p2m_e46e8dd0_1680_4d93_a7d5_10e0bd7d8348_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T00:23:44.818995+00:00
-- url     : https://prove2.me/theorems/1722b9cf-e3a4-4da3-a957-e71bc2edbef9
-- title:
--   Connected planar edge count bound
-- statement:
--   A finite connected simple graph with a crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges. This is the remaining Euler-formula argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_count_bound__p2m_e46e8dd0_1680_4d93_a7d5_10e0bd7d8348_a4 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hconn : G.Connected) (hCard : 3 <= Fintype.card V) : G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
