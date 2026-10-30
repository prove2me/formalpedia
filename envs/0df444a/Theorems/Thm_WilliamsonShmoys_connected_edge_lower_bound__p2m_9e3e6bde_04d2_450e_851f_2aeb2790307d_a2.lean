-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_edge_lower_bound__p2m_9e3e6bde_04d2_450e_851f_2aeb2790307d_a2
-- name    : WilliamsonShmoys_connected_edge_lower_bound__p2m_9e3e6bde_04d2_450e_851f_2aeb2790307d_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T08:29:55.807992+00:00
-- url     : https://prove2.me/theorems/f8834dc5-abd9-473a-a471-c949ea0c8f43
-- title:
--   Connected finite graphs have enough edges
-- statement:
--   A finite connected graph has at least one fewer edge than vertices. This yields positivity of the face count from Euler’s equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys_connected_edge_lower_bound__p2m_9e3e6bde_04d2_450e_851f_2aeb2790307d_a2 {V : Type} [Fintype V] (G : SimpleGraph V) (hConnected : G.Connected) : Fintype.card V ≤ G.edgeSet.ncard + 1 := by sorry
