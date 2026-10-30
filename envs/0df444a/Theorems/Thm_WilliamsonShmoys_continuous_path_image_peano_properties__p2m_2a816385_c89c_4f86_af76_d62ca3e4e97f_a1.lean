-- Prove2me | Theorems.Thm_WilliamsonShmoys_continuous_path_image_peano_properties__p2m_2a816385_c89c_4f86_af76_d62ca3e4e97f_a1
-- name    : WilliamsonShmoys.continuous_path_image_peano_properties__p2m_2a816385_c89c_4f86_af76_d62ca3e4e97f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:02:27.931748+00:00
-- url     : https://prove2.me/theorems/3c2e7bbf-7ada-4595-a5f9-d708bf50f324
-- title:
--   Continuous path images are Peano continua
-- statement:
--   The range of a continuous map restricted to [0,1] is compact, path-connected, and locally connected as a subspace of the plane.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.continuous_path_image_peano_properties__p2m_2a816385_c89c_4f86_af76_d62ca3e4e97f_a1 (γ : ℝ → ℝ × ℝ) (hcont : ContinuousOn γ (Set.Icc 0 1)) : IsCompact (Set.range γ) ∧ IsPathConnected (Set.range γ) ∧ LocallyConnectedSpace (Set.range γ) := by sorry
