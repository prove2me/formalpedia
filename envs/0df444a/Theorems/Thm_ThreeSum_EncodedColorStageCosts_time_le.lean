-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorStageCosts_time_le
-- name    : ThreeSum.EncodedColorStageCosts.time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:56:46.927256+00:00
-- url     : https://prove2.me/theorems/ba783729-6093-4a23-b2f2-acf6b407baac
-- title:
--   Encoded Color Stage Costs: time le
-- statement:
--   The Encoded Color Stage Costs construction uses the time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorStageCosts.lean#L49-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorStageCosts.lean#L49-L56

import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Theorems.Thm_ThreeSum_ColorBandBounds_time_le
import Theorems.Thm_ThreeSum_EncodedColorSourcesCosts_time_le
import Theorems.Thm_ThreeSum_EncodedColorWantedCosts_time_le
import Theorems.Thm_ThreeSum_LightKaratsuba_time_le
import Theorems.Thm_ThreeSum_SourceFiniteCosts_time_le

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorStageCosts
open Scales BandScales ArithmeticStageBounds

theorem ThreeSum.EncodedColorStageCosts.time_le {n p P M U len : ℕ} [NeZero M] {xs : List ℤ}
    (hp : p ≤ P) (hlen : xs.length ≤ len) :
    LightEncodedColorWantedSources.time n p M U xs ≤ time n P M U len := by sorry
