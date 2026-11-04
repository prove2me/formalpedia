-- Prove2me | Theorems.Thm_ThreeSum_BinarySearch_locate_sound_w3sum_ac885d1
-- name    : ThreeSum.BinarySearch.locate_sound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:01:56.960681+00:00
-- url     : https://prove2.me/theorems/2e6cf126-66e0-4dfc-989f-3301992ea601
-- title:
--   Binary Search: locate sound
-- statement:
--   The Binary Search construction uses the locate sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinarySearch.lean#L111-L127
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinarySearch.lean#L111-L127

import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_BinarySearch
set_option autoImplicit false
open ThreeSum ThreeSum.BinarySearch

theorem ThreeSum.BinarySearch.locate_sound_w3sum_ac885d1 (lo hi : ℕ → ℤ) (n : ℕ) (x : ℤ)
    (hsorted : ∀ i j, i ≤ j → j < n → lo i ≤ lo j)
    {i : ℕ} (h : locate lo hi n x = some i) :
    i < n ∧ lo i ≤ x ∧ x ≤ hi i := by sorry
