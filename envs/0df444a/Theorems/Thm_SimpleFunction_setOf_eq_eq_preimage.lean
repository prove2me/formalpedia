-- Prove2me | Theorems.Thm_SimpleFunction_setOf_eq_eq_preimage
-- name    : SimpleFunction.setOf_eq_eq_preimage
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:22:12.661363+00:00
-- url     : https://prove2.me/theorems/09cf7921-4869-49f9-ac14-a7a6099d1163
-- title:
--   ProbabilityTheory_chapter_06_def_6_1_F000: SimpleFunction.setOf_eq_eq_preimage
-- statement:
--   Source theorem `SimpleFunction.setOf_eq_eq_preimage` extracted from `ProbabilityTheory.chapter_06.def_6_1`. The formal Lean declaration specifies the proposition.
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

theorem setOf_eq_eq_preimage (X : SimpleFunction Ω) (x : EReal) :
    {ω | X ω = x} = X ⁻¹' {x} := by
  sorry
end SimpleFunction
