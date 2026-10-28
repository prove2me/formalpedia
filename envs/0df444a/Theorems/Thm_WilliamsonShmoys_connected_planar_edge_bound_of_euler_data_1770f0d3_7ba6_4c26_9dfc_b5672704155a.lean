-- Prove2me | Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_of_euler_data_1770f0d3_7ba6_4c26_9dfc_b5672704155a
-- name    : WilliamsonShmoys.connected_planar_edge_bound_of_euler_data_1770f0d3_7ba6_4c26_9dfc_b5672704155a
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:04:02.546364+00:00
-- url     : https://prove2.me/theorems/cf6af6ac-20ae-474d-8901-4d18cd7955a1
-- title:
--   Edge bound from Euler face data
-- statement:
--   Given a finite graph and face count satisfying Euler’s equation and the total face-boundary length bound, its edge count is at most three times its vertex count minus six. Prove by substituting the Euler equality into the face inequality and using linear arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.connected_planar_edge_bound_of_euler_data_1770f0d3_7ba6_4c26_9dfc_b5672704155a {V : Type} [Fintype V] (K : SimpleGraph V) (F : ℕ) (heuler : Fintype.card V + F = K.edgeSet.ncard + 2) (hfaces : 3 * F ≤ 2 * K.edgeSet.ncard) : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
