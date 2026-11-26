-- Prove2me | Theorems.Thm_Sqrt6KissingBound_kissingNumber_universal_base_iff
-- name    : Sqrt6KissingBound.kissingNumber_universal_base_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T06:18:46.565473+00:00
-- url     : https://prove2.me/theorems/f83eab67-725d-40a8-bfae-eed0a15aa0e4
-- title:
--   Sqrt6 Kissing Bound: kissing Number universal base iff
-- statement:
--   `√6` is the least nonnegative base bounding the actual kissing numbers.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/KissingNumber.lean#L125-L128
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/KissingNumber.lean#L125-L128

import Definitions.Def_Sqrt6KissingBound_Optimality
import Mathlib.Data.Nat.Find
import Definitions.Def_Sqrt6KissingBound_KissingNumber
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section

theorem Sqrt6KissingBound.kissingNumber_universal_base_iff (α : ℝ) :
    (0 ≤ α ∧ ∀ n : ℕ, 1 ≤ n → (kissingNumber n : ℝ) ≤ α ^ n) ↔
      Real.sqrt 6 ≤ α := by sorry
