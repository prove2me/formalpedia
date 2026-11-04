-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_length
-- name    : ThreeSum.TernaryWantedRadix.wantedCodes_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:18:41.388413+00:00
-- url     : https://prove2.me/theorems/014f2d9c-8fa2-486f-9675-9fcbdbd85e1b
-- title:
--   Ternary Wanted Radix: wanted Codes length
-- statement:
--   The Ternary Wanted Radix construction uses the wanted Codes length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedRadix.lean#L153-L155
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedRadix.lean#L153-L155

import Definitions.Def_Submission_ThreeSum_Radix
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedRadix
open Finset

theorem ThreeSum.TernaryWantedRadix.wantedCodes_length (p : ℤ) (raws : List ℤ) (j : ℕ) (x : ℤ) (code scale : ℕ) :
    (wantedCodes p raws j x code scale).length = (wantedOutputs p raws j x).length := by sorry
