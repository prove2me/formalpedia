-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorResources_normalized_space_bound
-- name    : ThreeSum.EncodedColorResources.normalized_space_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:46:45.710526+00:00
-- url     : https://prove2.me/theorems/b7aa6fe0-00ed-458c-aa08-e3e27d46f4fe
-- title:
--   Encoded Color Resources: normalized space bound
-- statement:
--   The Encoded Color Resources construction uses the normalized space bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeResources.lean#L33-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeResources.lean#L33-L37

import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeHost
import Definitions.Def_Submission_ThreeSum_EncodedColorPipelineData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open EncodedColorLayout KaratsubaInterface
set_option maxHeartbeats 2400000
set_option maxRecDepth 13000

theorem ThreeSum.EncodedColorResources.normalized_space_bound (free n : ℕ) :
    LightEncodedColorNormalize.space free n ≤ free+1000*(scale n)^3+1 := by sorry
