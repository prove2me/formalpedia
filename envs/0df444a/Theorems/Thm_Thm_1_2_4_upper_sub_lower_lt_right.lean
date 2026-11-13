-- Prove2me | Theorems.Thm_Thm_1_2_4_upper_sub_lower_lt_right
-- name    : Thm_1_2_4.upper_sub_lower_lt_right
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:12:00.246811+00:00
-- url     : https://prove2.me/theorems/d81de54e-bd83-4470-901e-54020cb62007
-- title:
--   Chapter 1, thm_1_2_4: Thm_1_2_4.upper_sub_lower_lt_right
-- statement:
--   Source theorem `Thm_1_2_4.upper_sub_lower_lt_right` from Chapter 1, module `thm_1_2_4`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic

noncomputable section Thm_1_2_4

namespace Thm_1_2_4

open scoped BigOperators Pointwise

noncomputable section SubintervalIntegrability

theorem upper_sub_lower_lt_right {a c b : ℝ} {f α : ℝ → ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ delta > 0, ∀ P2 : Partition c b, P2.mesh < delta →
      upperSum P2 f α - lowerSum P2 f α < eps := by sorry

end SubintervalIntegrability

end Thm_1_2_4  

end Thm_1_2_4
