-- Prove2me | Theorems.Thm_Thm_1_2_4_sourceHypotheses_right
-- name    : Thm_1_2_4.sourceHypotheses_right
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:53:58.153074+00:00
-- url     : https://prove2.me/theorems/e802c4ab-1b0e-436d-bcf6-cca4dda56917
-- title:
--   Chapter 1, thm_1_2_4: Thm_1_2_4.sourceHypotheses_right
-- statement:
--   Source theorem `Thm_1_2_4.sourceHypotheses_right` from Chapter 1, module `thm_1_2_4`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic

noncomputable section Thm_1_2_4

namespace Thm_1_2_4

open scoped BigOperators Pointwise

theorem sourceHypotheses_right {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (h : SourceHypotheses a b f α) :
    SourceHypotheses c b f α := by sorry

noncomputable section SubintervalIntegrability

end SubintervalIntegrability

end Thm_1_2_4  

end Thm_1_2_4
