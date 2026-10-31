-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_upper_bound__p2m_517acab8_1dff_430a_88ba_b65381dc6f37_a1
-- name    : WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_517acab8_1dff_430a_88ba_b65381dc6f37_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:31:06.979989+00:00
-- url     : https://prove2.me/theorems/3c187467-059b-4073-9a0b-83e3bfc104a1
-- title:
--   Connected planar simple graph edge-count bound
-- statement:
--   Every connected simple graph with a crossing-free drawing and at least three vertices has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_count_upper_bound__p2m_517acab8_1dff_430a_88ba_b65381dc6f37_a1 {V : Type} [Fintype V] [LinearOrder V] (Z : SimpleGraph V) (hconn : Z.Connected) (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) (hV : 3 ≤ Fintype.card V) : Z.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
