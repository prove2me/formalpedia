-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorWantedCosts_time_le
-- name    : ThreeSum.EncodedColorWantedCosts.time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:35:46.372174+00:00
-- url     : https://prove2.me/theorems/255cd308-9d66-4cff-a555-ea15d9202d6b
-- title:
--   Encoded Color Wanted Costs: time le
-- statement:
--   The Encoded Color Wanted Costs construction uses the time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorWantedCosts.lean#L35-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorWantedCosts.lean#L35-L41

import Definitions.Def_Submission_ThreeSum_LightEncodedColorWantedSources
import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Theorems.Thm_ThreeSum_ColorBandBounds_time_le
import Theorems.Thm_ThreeSum_EncodedColorSourcesCosts_time_le
import Theorems.Thm_ThreeSum_LightKaratsuba_time_le
import Theorems.Thm_ThreeSum_SourceFiniteCosts_time_le

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorWantedCosts
open Light WantedResidueKeys
set_option maxHeartbeats 1800000

theorem ThreeSum.EncodedColorWantedCosts.time_le (P M h J U : ℕ) [NeZero M] (xs : List ℤ) :
    LightGuardedWanted.time P M h J U xs ≤ time P M h J U xs.length := by sorry
