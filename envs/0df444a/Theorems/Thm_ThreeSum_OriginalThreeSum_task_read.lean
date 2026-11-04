-- Prove2me | Theorems.Thm_ThreeSum_OriginalThreeSum_task_read
-- name    : ThreeSum.OriginalThreeSum.task_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:23:19.177363+00:00
-- url     : https://prove2.me/theorems/c66dd58f-bb5a-4615-9ddd-a3b14a3fa9d8
-- title:
--   Original Three Sum: task read
-- statement:
--   The Original Three Sum construction uses the task read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OriginalThreeSum.lean#L29-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/OriginalThreeSum.lean#L29-L32

import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_Submission_ThreeSumApsp_Programs_Tasks
import Definitions.Def_Submission_ThreeSum_OriginalThreeSum
set_option autoImplicit false
open ThreeSum ThreeSum.OriginalThreeSum
open Light ThreeSumApsp.Spec

theorem ThreeSum.OriginalThreeSum.task_read {x : VecInst} {μ : ℕ → ℤ} {fr : ℕ} (H : x.Pre μ fr) :
    ∀ i : Fin x.N, μ (x.a+i.val)=vecOf x.N x.X i := by sorry
