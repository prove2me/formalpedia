-- Prove2me | Theorems.Thm_Sqrt6KissingBound_kissingNumber_le_sqrt6_pow
-- name    : Sqrt6KissingBound.kissingNumber_le_sqrt6_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:17:51.840848+00:00
-- url     : https://prove2.me/theorems/fa20e86e-f90a-5ce7-a987-6dc8557eb991
-- title:
--   Sqrt6 Kissing Bound: kissing Number le sqrt6 pow
-- statement:
--   The theorem in the usual notation: the kissing number itself is at most
--   the `n`-th power of `√6`.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/KissingNumber.lean#L62-L66
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/KissingNumber.lean#L62-L66

import Definitions.Def_Sqrt6KissingBound_Optimality
import Mathlib.Data.Nat.Find
import Definitions.Def_Sqrt6KissingBound_KissingNumber
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section

theorem Sqrt6KissingBound.kissingNumber_le_sqrt6_pow {n : ℕ} (hn : 1 ≤ n) :
    (kissingNumber n : ℝ) ≤ (Real.sqrt 6) ^ n := by sorry
