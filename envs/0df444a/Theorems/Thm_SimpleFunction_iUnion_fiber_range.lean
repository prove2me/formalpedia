-- Prove2me | Theorems.Thm_SimpleFunction_iUnion_fiber_range
-- name    : SimpleFunction.iUnion_fiber_range
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:22:45.063869+00:00
-- url     : https://prove2.me/theorems/874dd809-e571-4689-8d18-10ee7907d214
-- title:
--   ProbabilityTheory_chapter_06_def_6_1_F000: SimpleFunction.iUnion_fiber_range
-- statement:
--   Source theorem `SimpleFunction.iUnion_fiber_range` extracted from `ProbabilityTheory.chapter_06.def_6_1`. The formal Lean declaration specifies the proposition.
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

theorem iUnion_fiber_range (X : SimpleFunction Ω) :
    (⋃ x ∈ X.range, X ⁻¹' ({x} : Set EReal)) = Set.univ := by
  sorry
end SimpleFunction
