-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedRadix_codeLimit_child
-- name    : ThreeSum.TernaryWantedRadix.codeLimit_child
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:18:54.649228+00:00
-- url     : https://prove2.me/theorems/fdd3ad51-ced4-4bc5-a15e-79cda4cd8e71
-- title:
--   Ternary Wanted Radix: code Limit child
-- statement:
--   The Ternary Wanted Radix construction uses the code Limit child property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedRadix.lean#L146-L151
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedRadix.lean#L146-L151

import Definitions.Def_Submission_ThreeSum_Radix
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedRadix
open Finset

theorem ThreeSum.TernaryWantedRadix.codeLimit_child {N code scale j i : ℕ} (hN : 1 ≤ N) (hi : i < N) :
    codeLimit N (code+scale*i) (scale*N) j ≤ codeLimit N code scale (j+1) := by sorry
