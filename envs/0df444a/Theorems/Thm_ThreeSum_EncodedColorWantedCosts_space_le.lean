-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorWantedCosts_space_le
-- name    : ThreeSum.EncodedColorWantedCosts.space_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:25:50.041343+00:00
-- url     : https://prove2.me/theorems/d390648b-83e6-4f1a-b09c-b2b5da71c071
-- title:
--   Encoded Color Wanted Costs: space le
-- statement:
--   The Encoded Color Wanted Costs construction uses the space le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorWantedCosts.lean#L62-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorWantedCosts.lean#L62-L67

import Definitions.Def_Submission_ThreeSum_LightEncodedColorWantedSources
import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Theorems.Thm_ThreeSum_ColorBandBounds_space_le
import Theorems.Thm_ThreeSum_SourceFiniteCosts_space_le

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorWantedCosts
open Light WantedResidueKeys
set_option maxHeartbeats 1800000

theorem ThreeSum.EncodedColorWantedCosts.space_le (free P M h J U : ℕ) [NeZero M] (xs : List ℤ) :
    LightGuardedWanted.space free P M h J U xs ≤ space free P M h J U xs.length := by sorry
