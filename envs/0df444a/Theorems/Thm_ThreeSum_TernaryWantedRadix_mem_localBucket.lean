-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_localBucket
-- name    : ThreeSum.TernaryWantedRadix.mem_localBucket
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:18:43.958823+00:00
-- url     : https://prove2.me/theorems/d7369926-312f-488a-be8b-6549d07ff240
-- title:
--   Ternary Wanted Radix: mem local Bucket
-- statement:
--   The Ternary Wanted Radix construction uses the mem local Bucket property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedRadix.lean#L13-L15
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedRadix.lean#L13-L15

import Definitions.Def_Submission_ThreeSum_Radix
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedRadix
open Finset

theorem ThreeSum.TernaryWantedRadix.mem_localBucket (p : ℤ) (raws : List ℤ) (x : ℤ) (i : ℕ) :
    i ∈ localBucket p raws x ↔ i < raws.length ∧ p ∣ x-raws.getD i 0 := by sorry
