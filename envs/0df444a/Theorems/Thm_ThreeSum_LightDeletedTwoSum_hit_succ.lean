-- Prove2me | Theorems.Thm_ThreeSum_LightDeletedTwoSum_hit_succ
-- name    : ThreeSum.LightDeletedTwoSum.hit_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:07:14.600188+00:00
-- url     : https://prove2.me/theorems/a0bee529-4ffd-4229-af8d-a11f7dc0042d
-- title:
--   Light Deleted Two Sum: hit succ
-- statement:
--   The Light Deleted Two Sum construction uses the hit succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDeletedTwoSum.lean#L24-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDeletedTwoSum.lean#L24-L36

import Definitions.Def_Submission_ThreeSum_LightColoredTwoSum
import Definitions.Def_Submission_ThreeSum_LightOriginalBucketFilter
import Definitions.Def_Submission_ThreeSum_LightDeletedTwoSum
import Theorems.Thm_ThreeSum_LightColoredTwoSum_hit_succ

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightDeletedTwoSum
open Light ThreeSum.LightSubsetAddress
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

theorem ThreeSum.LightDeletedTwoSum.hit_succ (ids : ℕ → ℕ) (values scan target : ℕ → ℤ) (targetN scanN j : ℕ) (sign : ℤ) :
    Hit ids values scan target targetN scanN (j+1) sign ↔
      Hit ids values scan target targetN scanN j sign ∨
        LightColoredTwoSum.Hit scan target targetN scanN (values (ids j)) sign := by sorry
