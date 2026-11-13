-- Prove2me | Theorems.Thm_Thm61Support_integralValue_neg_of_defined
-- name    : Thm61Support.integralValue_neg_of_defined
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:26:15.941946+00:00
-- url     : https://prove2.me/theorems/2a13f84a-530c-4bc5-956a-1df0d1d873b3
-- title:
--   Chapter 6, thm_6_1: Thm61Support.integralValue_neg_of_defined
-- statement:
--   Source theorem `Thm61Support.integralValue_neg_of_defined` from Chapter 6, module `thm_6_1`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/thm_6_1.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic

open MeasureTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

namespace Thm61Support

theorem integralValue_neg_of_defined (μ : Measure Ω) (X : SimpleFunc Ω EReal)
    (hXdef : simpleFunctionIntegralDefined μ X) :
    simpleFunctionIntegralValue μ (X.map fun x => -x) =
      -simpleFunctionIntegralValue μ X := by sorry

end Thm61Support
