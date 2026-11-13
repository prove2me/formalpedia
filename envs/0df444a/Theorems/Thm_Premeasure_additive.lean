-- Prove2me | Theorems.Thm_Premeasure_additive
-- name    : Premeasure.additive
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T15:33:00.624391+00:00
-- url     : https://prove2.me/theorems/3e9d85f9-9fcd-413e-9139-1561aaa15a0b
-- title:
--   Chapter 3, def_3_1: Premeasure.additive
-- statement:
--   Source theorem `Premeasure.additive` from Chapter 3, module `def_3_1`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/def_3_1.lean

import Definitions.Def_ProbabilityTheory_chapter_03_def_3_1_F000
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Tactic

open Set ENNReal Function MeasureTheory

namespace FieldOfSets

end FieldOfSets

namespace Premeasure

variable {Ω : Type*} {F₀ : FieldOfSets Ω}

theorem additive (pm : Premeasure F₀) {s t : Set Ω}
    (hs : s ∈ F₀.carrier) (ht : t ∈ F₀.carrier) (hst : Disjoint s t)
    (hut : s ∪ t ∈ F₀.carrier) :
    pm.μ₀ ⟨s ∪ t, hut⟩ = pm.μ₀ ⟨s, hs⟩ + pm.μ₀ ⟨t, ht⟩ := by sorry

end Premeasure
