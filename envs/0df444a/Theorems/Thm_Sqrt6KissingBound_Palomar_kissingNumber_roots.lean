-- Prove2me | Theorems.Thm_Sqrt6KissingBound_Palomar_kissingNumber_roots
-- name    : Sqrt6KissingBound.Palomar.kissingNumber_roots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:26:54.6928+00:00
-- url     : https://prove2.me/theorems/a0bac282-61f3-5bfc-b176-453546aaefe1
-- title:
--   Palomar: kissing Number roots
-- statement:
--   The Palomar construction uses the kissing Number roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Solution.lean#L27-L48
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Solution.lean#L27-L48

import Definitions.Def_Sqrt6KissingBound
import Definitions.Def_Sqrt6KissingBound_Solution
set_option autoImplicit true
open Sqrt6KissingBound Sqrt6KissingBound.Palomar
noncomputable section

theorem Sqrt6KissingBound.Palomar.kissingNumber_roots (τ : ℕ → ℕ)
    (hτ : ∀ n : ℕ, 1 ≤ n →
      IsGreatest {m : ℕ | RealizableKissingCard n m} (τ n)) :
    sSup {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧
      r = (τ n : ℝ) ^ ((n : ℝ)⁻¹)} = Real.sqrt 6 := by sorry
