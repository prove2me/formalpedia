-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_succ
-- name    : ThreeSum.TernaryWantedRadix.wantedCodes_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:18:46.920221+00:00
-- url     : https://prove2.me/theorems/6ed78ad1-3fdf-446b-87d8-7e0939ba86b7
-- title:
--   Ternary Wanted Radix: wanted Codes succ
-- statement:
--   The Ternary Wanted Radix construction uses the wanted Codes succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedRadix.lean#L94-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedRadix.lean#L94-L97

import Definitions.Def_Submission_ThreeSum_Radix
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedRadix
open Finset

theorem ThreeSum.TernaryWantedRadix.wantedCodes_succ (p : ℤ) (raws : List ℤ) (j : ℕ) (x : ℤ) (code scale : ℕ) :
    wantedCodes p raws (j+1) x code scale = (localBucket p raws x).flatMap fun i =>
      wantedCodes p raws j ((x-raws.getD i 0)/p) (code+scale*i) (scale*raws.length) := by sorry
