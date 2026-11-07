-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat15_compensated_smear_algebra
-- name    : ProbabilityTheory.leanlevy_chat15_compensated_smear_algebra
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:18:32.410125+00:00
-- url     : https://prove2.me/theorems/002f7a5a-6af2-4b4c-83b1-3bc13f83bc36
-- title:
--   Algebraic compensated Fourier smear cancellation
-- statement:
--   For a symmetric Fourier average, the constant term and the linear compensator cancel exactly, leaving the oscillatory factor multiplied by one minus the sinc average.
-- source:
--   slink/LeanLevy 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineUniqueness.lean lines 206–215, algebraic core of levyCompensatedIntegrand_smear.

import Mathlib
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat15_compensated_smear_algebra (E L : ℂ) (s : ℝ) :
    (E - 1 - L) - (1 / 2 : ℂ) *
      (E * (2 * (s : ℂ)) - 2 - L * (2 : ℂ))
      = E * (1 - (s : ℂ)) := by sorry
