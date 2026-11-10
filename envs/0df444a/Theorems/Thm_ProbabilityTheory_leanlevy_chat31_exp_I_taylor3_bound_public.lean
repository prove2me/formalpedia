-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat31_exp_I_taylor3_bound_public
-- name    : ProbabilityTheory.leanlevy_chat31_exp_I_taylor3_bound_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:53:09.946667+00:00
-- url     : https://prove2.me/theorems/0575ed7e-7d41-4b2c-983a-0b8354f05f91
-- title:
--   Public third-order exponential Taylor bound on the imaginary axis
-- statement:
--   The imaginary-axis exponential has cubic third-order remainder bounded by (2/9)|z| cubed on the real unit interval.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L1286-L1338

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat31_exp_I_taylor3_bound_public {z : ℝ} (hz : |z| ≤ 1) :
    ‖Complex.exp ((↑z : ℂ) * I) - 1 - (↑z : ℂ) * I + (↑z : ℂ) ^ 2 / 2‖ ≤
      (2 / 9 : ℝ) * |z| ^ 3 := by sorry
