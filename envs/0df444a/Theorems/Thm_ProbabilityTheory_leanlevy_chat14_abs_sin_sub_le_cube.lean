-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat14_abs_sin_sub_le_cube
-- name    : ProbabilityTheory.leanlevy_chat14_abs_sin_sub_le_cube
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:10:10.880555+00:00
-- url     : https://prove2.me/theorems/87d5df3e-250c-4566-b744-1fac734d7cc8
-- title:
--   Local cubic sine-error estimate
-- statement:
--   Source-exact cubic sine error from third-order complex exponential Taylor bound at imaginary arguments.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineProof.lean, original abs_sin_sub_le_cube; CHAT14 proof unchanged; prior auto-strict job 498a8ea2 failed at preamble.

import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat14_abs_sin_sub_le_cube {x : ℝ} (hx : |x| ≤ 1) :
    |Real.sin x - x| ≤ 2 / 9 * |x| ^ 3 := by sorry
