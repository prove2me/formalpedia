-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_output_length
-- name    : ThreeSum.LightWeightedNearEnumeration.output_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:41:55.659029+00:00
-- url     : https://prove2.me/theorems/614f096b-597c-4873-bc76-0ec6787c1ffc
-- title:
--   Light Weighted Near Enumeration: output length
-- statement:
--   The Light Weighted Near Enumeration construction uses the output length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightNearEnumeration.lean#L36-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightNearEnumeration.lean#L36-L37

import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_LightNearEnumeration
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_length


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedNearEnumeration
open Light ThreeSum.LightSubsetAddress ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.WeightedNearEnumeration
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedNearEnumeration.output_length (qs : List ℕ) (D pref : ℕ) :
    (output qs D pref).length = (words qs D).length := by sorry
