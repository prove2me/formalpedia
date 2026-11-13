-- Prove2me | Theorems.Thm_SimpleFunction_measurableSet_fiber
-- name    : SimpleFunction.measurableSet_fiber
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:22:01.631126+00:00
-- url     : https://prove2.me/theorems/334c7caa-f4b7-4a3a-9271-6a994067532a
-- title:
--   ProbabilityTheory_chapter_06_def_6_1_F000: SimpleFunction.measurableSet_fiber
-- statement:
--   Source theorem `SimpleFunction.measurableSet_fiber` extracted from `ProbabilityTheory.chapter_06.def_6_1`. The formal Lean declaration specifies the proposition.
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

theorem measurableSet_fiber (X : SimpleFunction Ω) (x : EReal) :
    MeasurableSet (X ⁻¹' {x}) := by
  sorry
end SimpleFunction
