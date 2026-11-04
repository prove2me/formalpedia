-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_map_cons_output
-- name    : ThreeSum.LightWeightedNearEnumeration.map_cons_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:24:53.329399+00:00
-- url     : https://prove2.me/theorems/4434835f-2556-4aa2-a2a1-b2b852e91104
-- title:
--   Light Weighted Near Enumeration: map cons output
-- statement:
--   The Light Weighted Near Enumeration construction uses the map cons output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightNearEnumeration.lean#L44-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightNearEnumeration.lean#L44-L51

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

theorem ThreeSum.LightWeightedNearEnumeration.map_cons_output (qs : List ℕ) (D pref r : ℕ) :
    (words qs D).map (fun rs => ((pref+code (r::rs) : ℕ) : ℤ)) =
      output qs D (pref+digitCode r*4^qs.length) := by sorry
