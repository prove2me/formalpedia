-- Prove2me | Theorems.Thm_ThreeSum_LightColoredTwoSum_flag_zero
-- name    : ThreeSum.LightColoredTwoSum.flag_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:33:17.136961+00:00
-- url     : https://prove2.me/theorems/1280636b-1055-41c6-95cf-b1584455e7b2
-- title:
--   Light Colored Two Sum: flag zero
-- statement:
--   The Light Colored Two Sum construction uses the flag zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColoredTwoSum.lean#L37-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColoredTwoSum.lean#L37-L38

import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSum_LightColoredTwoSum
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightColoredTwoSum
open Light ThreeSum.LightSubsetAddress
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

theorem ThreeSum.LightColoredTwoSum.flag_zero (scan target : ℕ → ℤ) (m : ℕ) (bad sign : ℤ) :
    flag scan target m 0 bad sign=0 := by sorry
