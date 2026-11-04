-- Prove2me | Theorems.Thm_ThreeSum_BinarySearch_upperSearch_correct_w3sum_ac885d1
-- name    : ThreeSum.BinarySearch.upperSearch_correct_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:01:54.287749+00:00
-- url     : https://prove2.me/theorems/60f77d30-e08e-4c5e-b87e-33011c4ddb46
-- title:
--   Binary Search: upper Search correct
-- statement:
--   The Binary Search construction uses the upper Search correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinarySearch.lean#L51-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinarySearch.lean#L51-L87

import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_BinarySearch
set_option autoImplicit false
open ThreeSum ThreeSum.BinarySearch

theorem ThreeSum.BinarySearch.upperSearch_correct_w3sum_ac885d1 (f : ℕ → ℤ) (x : ℤ) (n fuel lo hi : ℕ)
    (hsorted : ∀ i j, i ≤ j → j < n → f i ≤ f j)
    (hlo : lo ≤ hi) (hhi : hi ≤ n) (hwidth : hi - lo < 2 ^ fuel)
    (hlower : ∀ i < lo, f i ≤ x)
    (hupper : ∀ i, hi ≤ i → i < n → x < f i) :
    Partition f x n (upperSearch f x fuel lo hi) := by sorry
