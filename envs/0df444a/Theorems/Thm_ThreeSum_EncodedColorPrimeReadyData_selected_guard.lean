-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorPrimeReadyData_selected_guard
-- name    : ThreeSum.EncodedColorPrimeReadyData.selected_guard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:47:46.878271+00:00
-- url     : https://prove2.me/theorems/3380b799-1deb-4acf-812b-1d81ce36af1d
-- title:
--   Encoded Color Prime Ready Data: selected guard
-- statement:
--   The Encoded Color Prime Ready Data construction uses the selected guard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeReadyData.lean#L34-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeReadyData.lean#L34-L37

import Definitions.Def_Submission_ThreeSum_EncodedColorNormalizedData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeReadyData
set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorPrimeReadyData
open Light Scales BandScales ColorClassLists EncodedColorLayout EncodedColorNormalizedData

theorem ThreeSum.EncodedColorPrimeReadyData.selected_guard {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hR : 4 ≤ radix n) : 4*selected n A B C hsA hsB hsC ≤ radix n := by sorry
