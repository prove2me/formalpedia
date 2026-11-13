-- Prove2me | Theorems.Thm_Thm_1_2_4_tag_le_upperStep
-- name    : Thm_1_2_4.tag_le_upperStep
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:45:24.469945+00:00
-- url     : https://prove2.me/theorems/efbdc72b-06c9-4ada-ae77-30030a0b85b2
-- title:
--   Source theorem: Thm_1_2_4.tag_le_upperStep
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

theorem tag_le_upperStep {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) (i : Fin P.n) {f : ℝ → ℝ}
    (hAbove : BddAbove (f '' Set.Icc a b)) :
    f (tags i) ≤ upperStep P f i := by
  sorry
end SubintervalIntegrability
end Thm_1_2_4
end Thm_1_2_4
