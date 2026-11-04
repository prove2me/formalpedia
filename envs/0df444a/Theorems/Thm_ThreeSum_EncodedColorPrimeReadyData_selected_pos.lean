-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorPrimeReadyData_selected_pos
-- name    : ThreeSum.EncodedColorPrimeReadyData.selected_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:56:45.028347+00:00
-- url     : https://prove2.me/theorems/e4184322-d7fb-4c27-924e-f7b6ae28d5c3
-- title:
--   Encoded Color Prime Ready Data: selected pos
-- statement:
--   The Encoded Color Prime Ready Data construction uses the selected pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeReadyData.lean#L29-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeReadyData.lean#L29-L32

import Definitions.Def_Submission_ThreeSum_EncodedColorNormalizedData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorPrimeReadyData
open Light Scales BandScales ColorClassLists EncodedColorLayout EncodedColorNormalizedData

theorem ThreeSum.EncodedColorPrimeReadyData.selected_pos {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} :
    0 < selected n A B C hsA hsB hsC := by sorry
