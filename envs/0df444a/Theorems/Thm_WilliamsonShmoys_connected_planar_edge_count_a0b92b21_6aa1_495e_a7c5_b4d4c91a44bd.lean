-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_a0b92b21_6aa1_495e_a7c5_b4d4c91a44bd
-- name    : WilliamsonShmoys.connected_planar_edge_count_a0b92b21_6aa1_495e_a7c5_b4d4c91a44bd
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T01:18:34.317132+00:00
-- url     : https://prove2.me/theorems/39075a03-fc95-43d7-ad3c-6ec5ef3a03b9
-- title:
--   Edge bound for connected planar graphs
-- statement:
--   A finite connected simple graph with the specified planar drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.connected_planar_edge_count_a0b92b21_6aa1_495e_a7c5_b4d4c91a44bd {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hconnected : H.Connected) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
