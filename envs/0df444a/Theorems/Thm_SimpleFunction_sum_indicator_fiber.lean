-- Prove2me | Theorems.Thm_SimpleFunction_sum_indicator_fiber
-- name    : SimpleFunction.sum_indicator_fiber
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:23:00.069058+00:00
-- url     : https://prove2.me/theorems/8c76ebd2-7a4f-4e31-8892-8214e38dcc1b
-- title:
--   Chapter 6, def_6_1: SimpleFunction.sum_indicator_fiber
-- statement:
--   Source theorem `SimpleFunction.sum_indicator_fiber` from Chapter 6, module `def_6_1`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/def_6_1.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_1_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open MeasureTheory
open scoped BigOperators

namespace SimpleFunction

variable {Ω : Type*} [MeasurableSpace Ω]

theorem sum_indicator_fiber (X : SimpleFunction Ω) :
    X = fun ω => ∑ x ∈ X.range, Set.indicator (X ⁻¹' ({x} : Set EReal)) (fun _ => x) ω := by sorry

end SimpleFunction
