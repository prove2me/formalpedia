-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_visits_cons
-- name    : ThreeSum.LightWeightedNearEnumeration.visits_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:24:55.177706+00:00
-- url     : https://prove2.me/theorems/2e342d1d-ebd5-4ae7-b961-f3a224513c39
-- title:
--   Light Weighted Near Enumeration: visits cons
-- statement:
--   The Light Weighted Near Enumeration construction uses the visits cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightNearEnumeration.lean#L69-L74
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightNearEnumeration.lean#L69-L74

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

theorem ThreeSum.LightWeightedNearEnumeration.visits_cons (q : Fin 3) (qs : List ℕ) (D : ℕ) :
    visits (q.val::qs) D = 1+branchVisits qs D q.val 0+
      branchVisits qs D q.val 1+branchVisits qs D q.val 2 := by sorry
