-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat24_tendsto_mul_one_sub_exp_div
-- name    : ProbabilityTheory.leanlevy_chat24_tendsto_mul_one_sub_exp_div
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T13:11:57.336118+00:00
-- url     : https://prove2.me/theorems/dad6ef6a-1720-4c2a-b577-043a9ed7f647
-- title:
--   Complex exponential scaled-difference limit for the Levy exponent
-- statement:
--   For every complex number z, the scaled difference m times one minus exp(z divided by m) converges to minus z, as needed for conditional negative definiteness of the Levy exponent.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineProof.lean lines 668-714, original private theorem tendsto_mul_one_sub_exp_div

import Mathlib

open Filter Complex

theorem ProbabilityTheory.leanlevy_chat24_tendsto_mul_one_sub_exp_div (z : ℂ) : Tendsto (fun m : ℕ => (↑m : ℂ) * (1 - exp (z / ↑m))) atTop (nhds (-z)) := by sorry
