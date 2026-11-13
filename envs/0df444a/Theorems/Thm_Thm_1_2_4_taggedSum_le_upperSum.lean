-- Prove2me | Theorems.Thm_Thm_1_2_4_taggedSum_le_upperSum
-- name    : Thm_1_2_4.taggedSum_le_upperSum
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:45:50.328294+00:00
-- url     : https://prove2.me/theorems/e7921340-04bd-48af-834d-0c224fd7057d
-- title:
--   Source theorem: Thm_1_2_4.taggedSum_le_upperSum
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

theorem taggedSum_le_upperSum {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) {f α : ℝ → ℝ} (hs : SourceHypotheses a b f α) :
    taggedSum P tags f α ≤ upperSum P f α := by
  sorry
end SubintervalIntegrability
end Thm_1_2_4
end Thm_1_2_4
