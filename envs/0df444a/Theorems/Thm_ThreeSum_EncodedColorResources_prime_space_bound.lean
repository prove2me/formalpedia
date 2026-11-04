-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorResources_prime_space_bound
-- name    : ThreeSum.EncodedColorResources.prime_space_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:48:17.891388+00:00
-- url     : https://prove2.me/theorems/779dd6aa-3420-4126-8c39-7b8a16f06c72
-- title:
--   Encoded Color Resources: prime space bound
-- statement:
--   The Encoded Color Resources construction uses the prime space bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeResources.lean#L160-L168
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeResources.lean#L160-L168

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

theorem ThreeSum.EncodedColorResources.prime_space_bound (free n U : ℕ) :
    LightEncodedColorPrimeHost.inputSpace free n U ≤ free+2000*(scale n)^3+U := by sorry
