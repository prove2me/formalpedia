-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_wantedOutputs
-- name    : ThreeSum.TernaryWantedRadix.mem_wantedOutputs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:18:58.721627+00:00
-- url     : https://prove2.me/theorems/8eb300b4-7b10-4aad-a884-de1abb1c04f7
-- title:
--   Ternary Wanted Radix: mem wanted Outputs
-- statement:
--   The Ternary Wanted Radix construction uses the mem wanted Outputs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedRadix.lean#L26-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedRadix.lean#L26-L46

import Definitions.Def_Submission_ThreeSum_Radix
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedRadix
open Finset

theorem ThreeSum.TernaryWantedRadix.mem_wantedOutputs (p : ℤ) (hp : p ≠ 0) (raws : List ℤ) :
    ∀ j x is, is ∈ wantedOutputs p raws j x ↔
      is.length=j ∧ (∀ i ∈ is, i < raws.length) ∧
      p^j ∣ x-Radix.positionalHash p (fun i => raws.getD i 0) is := by sorry
