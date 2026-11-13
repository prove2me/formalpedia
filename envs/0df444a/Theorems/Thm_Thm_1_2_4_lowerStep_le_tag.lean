-- Prove2me | Theorems.Thm_Thm_1_2_4_lowerStep_le_tag
-- name    : Thm_1_2_4.lowerStep_le_tag
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:45:39.003826+00:00
-- url     : https://prove2.me/theorems/e8a0c856-d561-4701-9ab4-291eb403058a
-- title:
--   Source theorem: Thm_1_2_4.lowerStep_le_tag
-- statement:
--   Original source theorem extracted from ProbabilityTheory.chapter_01.thm_1_2_4. Type preserved exactly.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F000
import Mathlib.Tactic
noncomputable section Thm_1_2_4
namespace Thm_1_2_4
open scoped BigOperators Pointwise
noncomputable section SubintervalIntegrability

theorem lowerStep_le_tag {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) (i : Fin P.n) {f : ℝ → ℝ}
    (hBelow : BddBelow (f '' Set.Icc a b)) :
    lowerStep P f i ≤ f (tags i) := by
  sorry
end SubintervalIntegrability
end Thm_1_2_4
end Thm_1_2_4
