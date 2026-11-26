-- Prove2me | Theorems.Thm_Sqrt6KissingBound_supremum_kissingNumber_roots_eq_sqrt6
-- name    : Sqrt6KissingBound.supremum_kissingNumber_roots_eq_sqrt6
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T06:18:39.977017+00:00
-- url     : https://prove2.me/theorems/d9f53ad3-353c-47b8-bd08-0b79d16b3665
-- title:
--   Sqrt6 Kissing Bound: supremum kissing Number roots eq sqrt6
-- statement:
--   The supremum of the dimensional roots of the kissing numbers is `√6`.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/KissingNumber.lean#L86-L104
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/KissingNumber.lean#L86-L104

import Definitions.Def_Sqrt6KissingBound_Optimality
import Mathlib.Data.Nat.Find
import Definitions.Def_Sqrt6KissingBound_KissingNumber
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section

theorem Sqrt6KissingBound.supremum_kissingNumber_roots_eq_sqrt6 :
    sSup {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧
      r = (kissingNumber n : ℝ) ^ ((n : ℝ)⁻¹)} = Real.sqrt 6 := by sorry
