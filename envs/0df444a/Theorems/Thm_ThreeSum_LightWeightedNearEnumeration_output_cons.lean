-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_output_cons
-- name    : ThreeSum.LightWeightedNearEnumeration.output_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:24:50.980017+00:00
-- url     : https://prove2.me/theorems/88782efc-e9e5-44ad-8594-542533662c47
-- title:
--   Light Weighted Near Enumeration: output cons
-- statement:
--   The Light Weighted Near Enumeration construction uses the output cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightNearEnumeration.lean#L53-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightNearEnumeration.lean#L53-L67

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

theorem ThreeSum.LightWeightedNearEnumeration.output_cons (q : Fin 3) (qs : List ℕ) (D pref : ℕ) :
    output (q.val::qs) D pref = branchOutput qs D pref q.val 0 ++
      branchOutput qs D pref q.val 1 ++ branchOutput qs D pref q.val 2 := by sorry
