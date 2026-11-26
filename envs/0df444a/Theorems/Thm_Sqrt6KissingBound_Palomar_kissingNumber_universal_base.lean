-- Prove2me | Theorems.Thm_Sqrt6KissingBound_Palomar_kissingNumber_universal_base
-- name    : Sqrt6KissingBound.Palomar.kissingNumber_universal_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:26:55.061398+00:00
-- url     : https://prove2.me/theorems/6889b5ce-d6ea-5001-a3b5-74c2d9654251
-- title:
--   Palomar: kissing Number universal base
-- statement:
--   The Palomar construction uses the kissing Number universal base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Solution.lean#L50-L68
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Solution.lean#L50-L68

import Definitions.Def_Sqrt6KissingBound
import Definitions.Def_Sqrt6KissingBound_Solution
set_option autoImplicit true
open Sqrt6KissingBound Sqrt6KissingBound.Palomar
noncomputable section

theorem Sqrt6KissingBound.Palomar.kissingNumber_universal_base (τ : ℕ → ℕ)
    (hτ : ∀ n : ℕ, 1 ≤ n →
      IsGreatest {m : ℕ | RealizableKissingCard n m} (τ n)) (α : ℝ) :
    (0 ≤ α ∧ ∀ n : ℕ, 1 ≤ n → (τ n : ℝ) ≤ α ^ n) ↔
      Real.sqrt 6 ≤ α := by sorry
