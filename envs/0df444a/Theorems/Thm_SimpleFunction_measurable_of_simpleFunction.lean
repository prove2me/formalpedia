-- Prove2me | Theorems.Thm_SimpleFunction_measurable_of_simpleFunction
-- name    : SimpleFunction.measurable_of_simpleFunction
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:21:38.92734+00:00
-- url     : https://prove2.me/theorems/22817a88-6c17-4566-b0ad-29eedafc12ee
-- title:
--   ProbabilityTheory_chapter_06_def_6_1_F000: SimpleFunction.measurable_of_simpleFunction
-- statement:
--   Source theorem `SimpleFunction.measurable_of_simpleFunction` extracted from `ProbabilityTheory.chapter_06.def_6_1`. The formal Lean declaration specifies the proposition.
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

theorem measurable_of_simpleFunction (X : SimpleFunction Ω) : Measurable X := by
  sorry
end SimpleFunction
