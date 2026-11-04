-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorResources_prime_core_space_bound
-- name    : ThreeSum.EncodedColorResources.prime_core_space_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:48:41.510501+00:00
-- url     : https://prove2.me/theorems/0e0beff0-4a46-4287-940e-fbf62eded8e1
-- title:
--   Encoded Color Resources: prime core space bound
-- statement:
--   The Encoded Color Resources construction uses the prime core space bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeResources.lean#L143-L158
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeResources.lean#L143-L158

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

theorem ThreeSum.EncodedColorResources.prime_core_space_bound (free n U : ℕ) :
    LightEncodedColorPrimeCore.space free (maxMod n) (bandSize n) (radix n) (primeWindow n) U ≤
      free+40*scale n+U+10 := by sorry
