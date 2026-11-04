-- Prove2me | Theorems.Thm_ThreeSum_OriginalThreeSum_flag_of_decision
-- name    : ThreeSum.OriginalThreeSum.flag_of_decision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:38:53.808572+00:00
-- url     : https://prove2.me/theorems/6a6be522-6461-4a6e-900a-79407523ef71
-- title:
--   Original Three Sum: flag of decision
-- statement:
--   The Original Three Sum construction uses the flag of decision property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OriginalThreeSum.lean#L18-L27
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OriginalThreeSum.lean#L18-L27

import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_Submission_ThreeSumApsp_Programs_Tasks
import Definitions.Def_Submission_ThreeSum_OriginalThreeSum
set_option autoImplicit false
open ThreeSum ThreeSum.OriginalThreeSum
open Light ThreeSumApsp.Spec

theorem ThreeSum.OriginalThreeSum.flag_of_decision {n : ℕ} (x : Fin n → ℤ) {r : ℤ}
    (hbool : r=0 ∨ r=1) (hcorrect : r=1 ↔ Coloring.DistinctZeroSum x) :
    r=ThreeSumApsp.flag (ThreeSumApsp.ThreeSum x) := by sorry
