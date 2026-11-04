-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorStageCosts_space_le
-- name    : ThreeSum.EncodedColorStageCosts.space_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:40:51.336584+00:00
-- url     : https://prove2.me/theorems/1a3d94a1-2e22-41a2-9cf4-dfa885e5af5d
-- title:
--   Encoded Color Stage Costs: space le
-- statement:
--   The Encoded Color Stage Costs construction uses the space le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorStageCosts.lean#L58-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorStageCosts.lean#L58-L63

import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
import Theorems.Thm_ThreeSum_ColorBandBounds_space_le
import Theorems.Thm_ThreeSum_EncodedColorWantedCosts_space_le
import Theorems.Thm_ThreeSum_SourceFiniteCosts_space_le

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorStageCosts
open Scales BandScales ArithmeticStageBounds

theorem ThreeSum.EncodedColorStageCosts.space_le {free n p P M U len : ℕ} [NeZero M] {xs : List ℤ}
    (hp : p ≤ P) (hlen : xs.length ≤ len) :
    LightEncodedColorWantedSources.space free n p M U xs ≤ space free n P M U len := by sorry
