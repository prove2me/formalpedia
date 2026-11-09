-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat24_tendsto_inv_mul_re_one_sub_exp
-- name    : ProbabilityTheory.leanlevy_chat24_tendsto_inv_mul_re_one_sub_exp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:16:50.730755+00:00
-- url     : https://prove2.me/theorems/8e6f17ff-6063-40d6-8063-5f25229a9017
-- title:
--   Real part of the scaled exponential difference converges
-- statement:
--   The real part of the inverse-time-scaled difference between one and the complex exponential converges to the negative real part of the exponent. Used for the Gaussian small-jump second-moment extraction.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineProof.lean lines 2219-2237 and dependent exp_first_order lines 1264-1288

import Mathlib

open Filter Complex Topology
open scoped Topology

theorem ProbabilityTheory.leanlevy_chat24_tendsto_inv_mul_re_one_sub_exp (z : ℂ) : Tendsto (fun t : ℝ => t⁻¹ * (1 - exp (↑t * z)).re) (𝓝[≠] 0) (𝓝 (-z).re) := by sorry
