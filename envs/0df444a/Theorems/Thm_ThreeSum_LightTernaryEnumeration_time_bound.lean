-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryEnumeration_time_bound
-- name    : ThreeSum.LightTernaryEnumeration.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:34:50.998315+00:00
-- url     : https://prove2.me/theorems/d3b957ee-f900-4c10-825b-91b660a21cb0
-- title:
--   Light Ternary Enumeration: time bound
-- statement:
--   The Light Ternary Enumeration construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEnumeration.lean#L93-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEnumeration.lean#L93-L95

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEnumeration
open Light ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryEnumeration.time_bound (N T : ℕ) :
    time N T ≤ 300*((N+1)*(codes N T).length) := by sorry
