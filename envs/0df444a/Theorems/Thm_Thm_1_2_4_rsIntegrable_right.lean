-- Prove2me | Theorems.Thm_Thm_1_2_4_rsIntegrable_right
-- name    : Thm_1_2_4.rsIntegrable_right
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:55:45.874834+00:00
-- url     : https://prove2.me/theorems/89cb464a-0620-4853-bc53-7dc2538b713b
-- title:
--   Source theorem: Thm_1_2_4.rsIntegrable_right
-- statement:
--   Source theorem extracted from ProbabilityTheory.chapter_01.thm_1_2_4, with its proposition and original proof recorded separately.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_4_F003
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_4_F000
import Mathlib.Tactic
noncomputable section Thm_1_2_4
namespace Thm_1_2_4
open scoped BigOperators Pointwise
noncomputable section SubintervalIntegrability

theorem rsIntegrable_right {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b) :
    RSIntegrable f α c b := by
  sorry
end SubintervalIntegrability
end Thm_1_2_4
end Thm_1_2_4
