-- Prove2me | Theorems.Thm_ThreeSum_LightBandEnumeration_lookup_sound
-- name    : ThreeSum.LightBandEnumeration.lookup_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:35:30.310826+00:00
-- url     : https://prove2.me/theorems/45187550-c3e1-4526-b0e5-186a00385a40
-- title:
--   Light Band Enumeration: lookup sound
-- statement:
--   The Light Band Enumeration construction uses the lookup sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandEnumeration.lean#L288-L298
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandEnumeration.lean#L288-L298

import Definitions.Def_Submission_ThreeSum_LightBandTable
import Definitions.Def_Submission_ThreeSum_BandEnumeration
import Definitions.Def_Submission_ThreeSum_LightCapacity
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_WeightedCache3SUM_Alias_183fd7d896c180f9

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandEnumeration
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
open Light ThreeSum.BandEnumeration ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBandEnumeration.lookup_sound (A : Family) {i : ℕ} {x : ℤ}
    (hr : LightBandLookup.result A.lower A.upper A.size x = i+1) :
    i < A.size ∧ A.lower i ≤ x ∧ x ≤ A.upper i := by sorry
