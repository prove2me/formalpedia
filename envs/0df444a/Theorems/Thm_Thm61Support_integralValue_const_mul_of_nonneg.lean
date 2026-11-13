-- Prove2me | Theorems.Thm_Thm61Support_integralValue_const_mul_of_nonneg
-- name    : Thm61Support.integralValue_const_mul_of_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:26:31.208227+00:00
-- url     : https://prove2.me/theorems/0ab15c9c-5e51-4238-8c80-71584cc7bfad
-- title:
--   Chapter 6, thm_6_1: Thm61Support.integralValue_const_mul_of_nonneg
-- statement:
--   Source theorem `Thm61Support.integralValue_const_mul_of_nonneg` from Chapter 6, module `thm_6_1`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/thm_6_1.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic

open MeasureTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

namespace Thm61Support

theorem integralValue_const_mul_of_nonneg (μ : Measure Ω) (X : SimpleFunc Ω EReal)
    (a : ℝ) (ha : 0 ≤ a) :
    simpleFunctionIntegralValue μ (X.map fun x => (a : EReal) * x) =
      (a : EReal) * simpleFunctionIntegralValue μ X := by sorry

end Thm61Support
