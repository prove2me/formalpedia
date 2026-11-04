-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorResources_normalized_word_bound
-- name    : ThreeSum.EncodedColorResources.normalized_word_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:52:02.821133+00:00
-- url     : https://prove2.me/theorems/2ea9e1cf-cafa-4d78-a108-74a3067cfcee
-- title:
--   Encoded Color Resources: normalized word bound
-- statement:
--   The Encoded Color Resources construction uses the normalized word bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeResources.lean#L63-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeResources.lean#L63-L73

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

theorem ThreeSum.EncodedColorResources.normalized_word_bound (n U : ℕ) : LightEncodedColorNormalize.word n U ≤ 400*(scale n)^2+9*U := by sorry
