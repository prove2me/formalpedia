-- Prove2me | Theorems.Thm_ThreeSum_BinarySearch_locate_complete_w3sum_ac885d1
-- name    : ThreeSum.BinarySearch.locate_complete_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:01:59.056223+00:00
-- url     : https://prove2.me/theorems/8c2761e7-a6d6-410e-959b-2eae02def2a4
-- title:
--   Binary Search: locate complete
-- statement:
--   The Binary Search construction uses the locate complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinarySearch.lean#L129-L146
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinarySearch.lean#L129-L146

import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_BinarySearch
set_option autoImplicit false
open ThreeSum ThreeSum.BinarySearch

theorem ThreeSum.BinarySearch.locate_complete_w3sum_ac885d1 (lo hi : ℕ → ℤ) (n : ℕ) (x : ℤ)
    (hsorted : ∀ i j, i ≤ j → j < n → lo i ≤ lo j)
    (hseparated : ∀ i j, i < j → j < n → hi i < lo j)
    {i : ℕ} (hin : i < n) (hil : lo i ≤ x) (hih : x ≤ hi i) :
    locate lo hi n x = some i := by sorry
