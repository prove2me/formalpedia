-- Prove2me | Theorems.Thm_ThreeSum_LightDeletedTwoSum_flag_le_one
-- name    : ThreeSum.LightDeletedTwoSum.flag_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:01:45.184352+00:00
-- url     : https://prove2.me/theorems/a1191cf2-7fe7-4830-ae48-536480711b7b
-- title:
--   Light Deleted Two Sum: flag le one
-- statement:
--   The Light Deleted Two Sum construction uses the flag le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDeletedTwoSum.lean#L21-L22
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDeletedTwoSum.lean#L21-L22

import Definitions.Def_Submission_ThreeSum_LightColoredTwoSum
import Definitions.Def_Submission_ThreeSum_LightOriginalBucketFilter
import Definitions.Def_Submission_ThreeSum_LightDeletedTwoSum
import Theorems.Thm_ThreeSum_LightColoredTwoSum_flag_le_one

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightDeletedTwoSum
open Light ThreeSum.LightSubsetAddress
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

theorem ThreeSum.LightDeletedTwoSum.flag_le_one (ids : ℕ → ℕ) (values scan target : ℕ → ℤ) (targetN scanN j : ℕ) (sign : ℤ) :
    flag ids values scan target targetN scanN j sign≤1 := by sorry
