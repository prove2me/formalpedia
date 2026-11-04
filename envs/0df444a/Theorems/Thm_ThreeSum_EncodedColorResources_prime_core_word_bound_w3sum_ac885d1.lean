-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorResources_prime_core_word_bound_w3sum_ac885d1
-- name    : ThreeSum.EncodedColorResources.prime_core_word_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:46:37.775744+00:00
-- url     : https://prove2.me/theorems/dfd74f12-84dc-427b-ba00-c9720f415f41
-- title:
--   Encoded Color Resources: prime core word bound
-- statement:
--   The Encoded Color Resources construction uses the prime core word bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeResources.lean#L78-L116
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeResources.lean#L78-L116

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

theorem ThreeSum.EncodedColorResources.prime_core_word_bound_w3sum_ac885d1 (n U : ℕ) :
    LightEncodedColorPrimeCore.word (maxMod n) n n n (bandSize n)
      (ColorBandBounds.count n (bandSize n)) (radix n) (primeWindow n) U ≤ 5000*(scale n)^6+4*U := by sorry
