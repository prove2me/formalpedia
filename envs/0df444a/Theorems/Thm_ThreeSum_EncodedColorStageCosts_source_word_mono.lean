-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorStageCosts_source_word_mono
-- name    : ThreeSum.EncodedColorStageCosts.source_word_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:06:30.618359+00:00
-- url     : https://prove2.me/theorems/b50af3d0-56a4-458a-972f-cf4434e63a11
-- title:
--   Encoded Color Stage Costs: source word mono
-- statement:
--   The Encoded Color Stage Costs construction uses the source word mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorStageCosts.lean#L38-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorStageCosts.lean#L38-L42

import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorStageCosts
open Scales BandScales ArithmeticStageBounds

theorem ThreeSum.EncodedColorStageCosts.source_word_mono {n p P U D : ℕ} (hp : p ≤ P) :
    SourceFiniteCosts.word n p U D ≤ SourceFiniteCosts.word n P U D := by sorry
