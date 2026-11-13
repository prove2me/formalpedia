-- Prove2me | Theorems.Thm_Thm_1_2_4_sourceHypotheses_left
-- name    : Thm_1_2_4.sourceHypotheses_left
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:53:46.393427+00:00
-- url     : https://prove2.me/theorems/5e57a6f9-fe29-4be3-b987-74e307818416
-- title:
--   Chapter 1, thm_1_2_4: Thm_1_2_4.sourceHypotheses_left
-- statement:
--   Source theorem `Thm_1_2_4.sourceHypotheses_left` from Chapter 1, module `thm_1_2_4`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2_4.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic

noncomputable section Thm_1_2_4

namespace Thm_1_2_4

open scoped BigOperators Pointwise

theorem sourceHypotheses_left {f α : ℝ → ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (h : SourceHypotheses a b f α) :
    SourceHypotheses a c f α := by sorry

noncomputable section SubintervalIntegrability

end SubintervalIntegrability

end Thm_1_2_4  

end Thm_1_2_4
