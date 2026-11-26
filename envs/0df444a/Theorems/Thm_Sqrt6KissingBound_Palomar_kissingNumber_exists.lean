-- Prove2me | Theorems.Thm_Sqrt6KissingBound_Palomar_kissingNumber_exists
-- name    : Sqrt6KissingBound.Palomar.kissingNumber_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:26:31.97997+00:00
-- url     : https://prove2.me/theorems/c66465be-50d9-505e-9828-4d3d5c1892bb
-- title:
--   Palomar: kissing Number exists
-- statement:
--   The Palomar construction uses the kissing Number exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Solution.lean#L16-L20
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Solution.lean#L16-L20

import Definitions.Def_Sqrt6KissingBound
import Definitions.Def_Sqrt6KissingBound_Solution
set_option autoImplicit true
open Sqrt6KissingBound Sqrt6KissingBound.Palomar
noncomputable section

theorem Sqrt6KissingBound.Palomar.kissingNumber_exists {n : ℕ} (hn : 1 ≤ n) :
    ∃ k : ℕ, IsGreatest {m : ℕ | RealizableKissingCard n m} k ∧
      (k : ℝ) ≤ (Real.sqrt 6) ^ n := by sorry
