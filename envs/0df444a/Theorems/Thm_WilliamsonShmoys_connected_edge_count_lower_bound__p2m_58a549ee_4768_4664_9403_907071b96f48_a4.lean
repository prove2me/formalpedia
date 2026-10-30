-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_edge_count_lower_bound__p2m_58a549ee_4768_4664_9403_907071b96f48_a4
-- name    : WilliamsonShmoys.connected_edge_count_lower_bound__p2m_58a549ee_4768_4664_9403_907071b96f48_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T05:53:46.057256+00:00
-- url     : https://prove2.me/theorems/8d099cf2-cac0-45a7-bb59-0ef1b2eb6592
-- title:
--   Connected graphs have at least one fewer edge than vertices
-- statement:
--   A finite connected simple graph has at least |V| − 1 edges, including the one-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.connected_edge_count_lower_bound__p2m_58a549ee_4768_4664_9403_907071b96f48_a4 {V : Type} [Fintype V] (H : SimpleGraph V) (hconn : H.Connected) : Fintype.card V ≤ H.edgeSet.ncard + 1 := by sorry
