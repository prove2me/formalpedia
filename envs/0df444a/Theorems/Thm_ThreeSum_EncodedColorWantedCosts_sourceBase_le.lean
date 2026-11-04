-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorWantedCosts_sourceBase_le
-- name    : ThreeSum.EncodedColorWantedCosts.sourceBase_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:43:35.169973+00:00
-- url     : https://prove2.me/theorems/93ac3005-b10f-43f9-a0eb-7624d143992a
-- title:
--   Encoded Color Wanted Costs: source Base le
-- statement:
--   The Encoded Color Wanted Costs construction uses the source Base le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorWantedCosts.lean#L51-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorWantedCosts.lean#L51-L60

import Definitions.Def_Submission_ThreeSum_LightEncodedColorWantedSources
import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorWantedCosts
open Light WantedResidueKeys
set_option maxHeartbeats 1800000

theorem ThreeSum.EncodedColorWantedCosts.sourceBase_le (free P M h J : ℕ) [NeZero M] (xs : List ℤ) :
    EncodedColorWantedData.nextFree (LightGuardedWanted.wantedFree free h J xs.length) M
      (LightGuardedWanted.left P xs) (LightGuardedWanted.right h J)
      (3*xs.length) (LightGuardedWanted.totalKeys h J) (RawAKeyLists.selected M P xs h J) ≤
        sourceBase free M h J xs.length := by sorry
