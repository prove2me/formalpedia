-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorSourcesCosts_time_le
-- name    : ThreeSum.EncodedColorSourcesCosts.time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:06:37.982843+00:00
-- url     : https://prove2.me/theorems/34c741f2-6572-4ca1-b861-b6e9406b6578
-- title:
--   Encoded Color Sources Costs: time le
-- statement:
--   The Encoded Color Sources Costs construction uses the time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorSourcesCosts.lean#L13-L18
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorSourcesCosts.lean#L13-L18

import Definitions.Def_Submission_ThreeSum_LightEncodedColorSources
import Definitions.Def_Submission_ThreeSum_SourceFiniteCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorSourcesCosts
import Theorems.Thm_ThreeSum_ColorBandBounds_time_le
import Theorems.Thm_ThreeSum_LightKaratsuba_time_le
import Theorems.Thm_ThreeSum_SourceFiniteCosts_time_le

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorSourcesCosts
open Scales TrimScales BandScales

theorem ThreeSum.EncodedColorSourcesCosts.time_le {NL NR n p U M : ℕ} (hn : 0 < n) (hL : NL ≤ n) (hR : NR ≤ n) :
    LightEncodedColorSources.time NL NR (bandSize n) p (microHalf (inputBits n))
      (blockCount (inputBits n)) (mu n) U M ≤ time n p U M := by sorry
