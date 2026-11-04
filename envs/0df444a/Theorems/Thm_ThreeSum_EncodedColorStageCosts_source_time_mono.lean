-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorStageCosts_source_time_mono
-- name    : ThreeSum.EncodedColorStageCosts.source_time_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:58:26.965038+00:00
-- url     : https://prove2.me/theorems/1491fe4f-07ed-4f88-8102-5c8725c3434f
-- title:
--   Encoded Color Stage Costs: source time mono
-- statement:
--   The Encoded Color Stage Costs construction uses the source time mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorStageCosts.lean#L28-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorStageCosts.lean#L28-L31

import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorStageCosts
open Scales BandScales ArithmeticStageBounds

theorem ThreeSum.EncodedColorStageCosts.source_time_mono {n p P U D : ℕ} (hp : p ≤ P) :
    EncodedColorSourcesCosts.time n p U D ≤ EncodedColorSourcesCosts.time n P U D := by sorry
