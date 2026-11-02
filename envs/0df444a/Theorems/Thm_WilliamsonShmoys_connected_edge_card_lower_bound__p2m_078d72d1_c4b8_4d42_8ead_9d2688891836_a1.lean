-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_edge_card_lower_bound__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1
-- name    : WilliamsonShmoys.connected_edge_card_lower_bound__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:42:43.673695+00:00
-- url     : https://prove2.me/theorems/b587b577-f5ff-4091-8d66-fbb60722febc
-- title:
--   A connected finite graph contains enough edges
-- statement:
--   Every finite connected simple graph has at least one fewer edge than vertices, as witnessed by a spanning tree.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_edge_card_lower_bound__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected) : Fintype.card V <= G.edgeFinset.card + 1 := by sorry
