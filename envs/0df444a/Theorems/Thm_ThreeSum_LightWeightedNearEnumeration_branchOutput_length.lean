-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_branchOutput_length
-- name    : ThreeSum.LightWeightedNearEnumeration.branchOutput_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:35:45.35514+00:00
-- url     : https://prove2.me/theorems/ec3407ee-1476-4d54-a0b6-8cf204166d2d
-- title:
--   Light Weighted Near Enumeration: branch Output length
-- statement:
--   The Light Weighted Near Enumeration construction uses the branch Output length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightNearEnumeration.lean#L39-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightNearEnumeration.lean#L39-L42

import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_LightNearEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedNearEnumeration
open Light ThreeSum.LightSubsetAddress ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.WeightedNearEnumeration
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedNearEnumeration.branchOutput_length (qs : List ℕ) (D pref q r : ℕ) :
    (branchOutput qs D pref q r).length = branchCount qs D q r := by sorry
