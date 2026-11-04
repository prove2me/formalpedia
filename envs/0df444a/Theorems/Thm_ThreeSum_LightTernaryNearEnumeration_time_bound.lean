-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryNearEnumeration_time_bound
-- name    : ThreeSum.LightTernaryNearEnumeration.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:41:19.683352+00:00
-- url     : https://prove2.me/theorems/1eaa9df5-2244-4fcc-b8d3-bb5e5a22e9e7
-- title:
--   Light Ternary Near Enumeration: time bound
-- statement:
--   The Light Ternary Near Enumeration construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearEnumeration.lean#L212-L214
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearEnumeration.lean#L212-L214

import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumeration
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearEnumeration
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryAddresses
open ThreeSum.TernaryNearEnumeration
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryNearEnumeration.time_bound (qs : List ℕ) (D : ℕ) :
    time qs D ≤ 900*((qs.length+1)*(words qs D).length) := by sorry
