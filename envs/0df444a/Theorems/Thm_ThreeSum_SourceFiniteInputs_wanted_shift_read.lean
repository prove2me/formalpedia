-- Prove2me | Theorems.Thm_ThreeSum_SourceFiniteInputs_wanted_shift_read
-- name    : ThreeSum.SourceFiniteInputs.wanted_shift_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:17:54.474553+00:00
-- url     : https://prove2.me/theorems/8de36e26-497e-4d37-a2a6-3f9e120bbcd7
-- title:
--   Source Finite Inputs: wanted shift read
-- statement:
--   The Source Finite Inputs construction uses the wanted shift read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteInputs.lean#L62-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteInputs.lean#L62-L67

import Definitions.Def_Submission_ThreeSum_LightGuardedWanted
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor
import Definitions.Def_Submission_ThreeSum_SourceBandFinite
import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteInputs
open Light GlobalEncoding LocalCoverBounds LightLocalCoverLayout LightLocalCoverSchedule

theorem ThreeSum.SourceFiniteInputs.wanted_shift_read {μ : ℕ → ℤ} {free M P h J : ℕ} [NeZero M] {xs : List ℤ}
    (H : LightWantedSetup.Output μ (LightGuardedWanted.wantedFree free h J xs.length) M
      (LightGuardedWanted.left P xs) (LightGuardedWanted.right h J)
      (3*xs.length) (LightGuardedWanted.totalKeys h J) (RawAKeyLists.selected M P xs h J)) :
    μ (LightGuardedWanted.wantedFree free h J xs.length+3)=(RawAKeyLists.selected M P xs h J : ℤ) := by sorry
