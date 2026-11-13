-- Prove2me | Theorems.Thm_Premeasure_toAddContent_apply
-- name    : Premeasure.toAddContent_apply
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T21:31:08.185992+00:00
-- url     : https://prove2.me/theorems/36cc12f3-71dd-4142-962f-a2daba11f6d0
-- title:
--   ProbabilityTheory_chapter_03_def_3_1_F001: Premeasure.toAddContent_apply
-- statement:
--   Source theorem `Premeasure.toAddContent_apply` extracted from `ProbabilityTheory.chapter_03.def_3_1`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/def_3_1.lean

import Definitions.Def_ProbabilityTheory_chapter_03_def_3_1_F001
import Definitions.Def_ProbabilityTheory_chapter_03_def_3_1_F000
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Tactic
open Set ENNReal Function MeasureTheory
namespace FieldOfSets
end FieldOfSets
namespace Premeasure
variable {Ω : Type*} {F₀ : FieldOfSets Ω}

theorem toAddContent_apply (pm : Premeasure F₀) (s : Set Ω) :
    pm.toAddContent s = pm.toSetFunction s := by
  sorry
attribute [simp] toAddContent_apply
end Premeasure
