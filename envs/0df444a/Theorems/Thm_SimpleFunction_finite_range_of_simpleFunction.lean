-- Prove2me | Theorems.Thm_SimpleFunction_finite_range_of_simpleFunction
-- name    : SimpleFunction.finite_range_of_simpleFunction
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:21:51.999195+00:00
-- url     : https://prove2.me/theorems/4dfe17b2-2a20-4625-a86f-72f1697cd5ee
-- title:
--   ProbabilityTheory_chapter_06_def_6_1_F000: SimpleFunction.finite_range_of_simpleFunction
-- statement:
--   Source theorem `SimpleFunction.finite_range_of_simpleFunction` extracted from `ProbabilityTheory.chapter_06.def_6_1`. The formal Lean declaration specifies the proposition.
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

theorem finite_range_of_simpleFunction (X : SimpleFunction Ω) : (Set.range X).Finite := by
  sorry
end SimpleFunction
