-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorResources_keyBound_le
-- name    : ThreeSum.EncodedColorResources.keyBound_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:41:03.935748+00:00
-- url     : https://prove2.me/theorems/1aedbdda-9888-4f45-b0fc-812efd24bd7a
-- title:
--   Encoded Color Resources: key Bound le
-- statement:
--   The Encoded Color Resources construction uses the key Bound le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorResourceScale.lean#L109-L116
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorResourceScale.lean#L109-L116

import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Definitions.Def_Submission_ThreeSum_LightBandRawAResourcesScales
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources
import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open Filter
set_option maxHeartbeats 2200000
set_option maxRecDepth 13000

theorem ThreeSum.EncodedColorResources.keyBound_le (n : ℕ) : LightGuardedWanted.keyBound (maxMod n) (half n) (blocks n) ≤ 3*(scale n)^4 := by sorry
