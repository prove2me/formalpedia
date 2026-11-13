-- Prove2me | Theorems.Thm_SimpleFunction_disjoint_fiber_of_ne
-- name    : SimpleFunction.disjoint_fiber_of_ne
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:22:29.294132+00:00
-- url     : https://prove2.me/theorems/e3bdca69-f483-43e1-929c-edca4223c345
-- title:
--   ProbabilityTheory_chapter_06_def_6_1_F000: SimpleFunction.disjoint_fiber_of_ne
-- statement:
--   Source theorem `SimpleFunction.disjoint_fiber_of_ne` extracted from `ProbabilityTheory.chapter_06.def_6_1`. The formal Lean declaration specifies the proposition.
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

theorem disjoint_fiber_of_ne (X : SimpleFunction Ω) {x y : EReal}
  (hxy : x ≠ y) :
    Disjoint (X ⁻¹' {x}) (X ⁻¹' {y}) := by
  sorry
end SimpleFunction
