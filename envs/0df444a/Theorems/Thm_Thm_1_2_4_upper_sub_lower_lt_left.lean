-- Prove2me | Theorems.Thm_Thm_1_2_4_upper_sub_lower_lt_left
-- name    : Thm_1_2_4.upper_sub_lower_lt_left
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:54:58.155455+00:00
-- url     : https://prove2.me/theorems/a9ee2f09-5eef-4fe5-a735-0a5cf7bef920
-- title:
--   Chapter 1, thm_1_2_4: Thm_1_2_4.upper_sub_lower_lt_left
-- statement:
--   Source theorem `Thm_1_2_4.upper_sub_lower_lt_left` from Chapter 1, module `thm_1_2_4`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic

noncomputable section Thm_1_2_4

namespace Thm_1_2_4

open scoped BigOperators Pointwise

noncomputable section SubintervalIntegrability

theorem upper_sub_lower_lt_left {a c b : ℝ} {f α : ℝ → ℝ}
    (hac : a < c) (hcb : c < b) (hab : RSIntegrable f α a b)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ delta > 0, ∀ P1 : Partition a c, P1.mesh < delta →
      upperSum P1 f α - lowerSum P1 f α < eps := by sorry

end SubintervalIntegrability

end Thm_1_2_4  

end Thm_1_2_4
