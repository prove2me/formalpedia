-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedRadix_child_target_bound
-- name    : ThreeSum.TernaryWantedRadix.child_target_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:18:57.623068+00:00
-- url     : https://prove2.me/theorems/02eba8ef-8734-445c-869f-f4679e544dd8
-- title:
--   Ternary Wanted Radix: child target bound
-- statement:
--   The Ternary Wanted Radix construction uses the child target bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedRadix.lean#L126-L136
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedRadix.lean#L126-L136

import Definitions.Def_Submission_ThreeSum_Radix
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedRadix
open Finset

theorem ThreeSum.TernaryWantedRadix.child_target_bound (p V : ℕ) (hp : 2 ≤ p) {x a : ℤ}
    (hx : |x| ≤ (V : ℤ)) (ha : |a| ≤ (V : ℤ)) (hdiv : (p : ℤ) ∣ x-a) :
    |(x-a)/(p : ℤ)| ≤ (V : ℤ) := by sorry
