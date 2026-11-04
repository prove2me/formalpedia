-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorStageCosts_selected_le_maxMod
-- name    : ThreeSum.EncodedColorStageCosts.selected_le_maxMod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:07:46.577199+00:00
-- url     : https://prove2.me/theorems/268d3764-c98e-4ff2-bac3-fa607a84d4e2
-- title:
--   Encoded Color Stage Costs: selected le max Mod
-- statement:
--   The Encoded Color Stage Costs construction uses the selected le max Mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorStageCosts.lean#L82-L91
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorStageCosts.lean#L82-L91

import Definitions.Def_Submission_ThreeSum_EncodedColorWantedCosts
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
import Definitions.Def_Submission_ThreeSum_EncodedColorStageCosts
set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorStageCosts
open Scales BandScales ArithmeticStageBounds

theorem ThreeSum.EncodedColorStageCosts.selected_le_maxMod {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hR : 4 ≤ radix n) : EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC ≤ maxMod n := by sorry
