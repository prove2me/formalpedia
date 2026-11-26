-- Prove2me | Theorems.Thm_Sqrt6KissingBound_integral_div_mul_pow
-- name    : Sqrt6KissingBound.integral_div_mul_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:02:58.955596+00:00
-- url     : https://prove2.me/theorems/53455125-641e-558a-9132-a4b598f8e15d
-- title:
--   Sqrt6 Kissing Bound: integral div mul pow
-- statement:
--   Integral of a power of a line through the origin.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/LinearProfileIntegral.lean#L14-L31
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/LinearProfileIntegral.lean#L14-L31

import Mathlib
import Definitions.Def_Sqrt6KissingBound_LinearProfileIntegral
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set
open scoped Interval Real
open intervalIntegral

theorem Sqrt6KissingBound.integral_div_mul_pow (m : ℕ) {a c : ℝ} (hc : c ≠ 0) :
    (∫ t in (0 : ℝ)..a, (t / c) ^ m) =
      a ^ (m + 1) / (c ^ m * (m + 1)) := by sorry
