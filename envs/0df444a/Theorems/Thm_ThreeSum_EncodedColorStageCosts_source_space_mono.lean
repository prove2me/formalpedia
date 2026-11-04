-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorStageCosts_source_space_mono
-- name    : ThreeSum.EncodedColorStageCosts.source_space_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:57:58.169932+00:00
-- url     : https://prove2.me/theorems/fd244150-1897-4c5b-b4fa-546604d9f12b
-- title:
--   Encoded Color Stage Costs: source space mono
-- statement:
--   The Encoded Color Stage Costs construction uses the source space mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorStageCosts.lean#L33-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorStageCosts.lean#L33-L36

import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorStageCosts
open Scales BandScales ArithmeticStageBounds

theorem ThreeSum.EncodedColorStageCosts.source_space_mono {base bound n p P U D : ℕ} (hb : base ≤ bound) (hp : p ≤ P) :
    SourceFiniteCosts.space base n p U D ≤ SourceFiniteCosts.space bound n P U D := by sorry
