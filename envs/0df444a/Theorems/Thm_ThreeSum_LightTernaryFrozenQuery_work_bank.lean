-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_work_bank
-- name    : ThreeSum.LightTernaryFrozenQuery.work_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:32:31.152803+00:00
-- url     : https://prove2.me/theorems/0b8fde2b-5d1f-4a86-af08-13de2828cbe3
-- title:
--   Light Ternary Frozen Query: work bank
-- statement:
--   The Light Ternary Frozen Query construction uses the work bank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryTime.lean#L15-L16
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryTime.lean#L15-L16

import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPrepare
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryTime
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryFrozenQueryCost
set_option maxHeartbeats 3000000

theorem ThreeSum.LightTernaryFrozenQuery.work_bank {N : ℕ} (T : ℕ) (is : List (Fin N)) (R : TritWord N)
    (h : rank R≤T) : work T is R=1 := by sorry
