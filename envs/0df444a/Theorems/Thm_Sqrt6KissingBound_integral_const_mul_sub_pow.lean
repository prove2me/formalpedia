-- Prove2me | Theorems.Thm_Sqrt6KissingBound_integral_const_mul_sub_pow
-- name    : Sqrt6KissingBound.integral_const_mul_sub_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:02:57.487714+00:00
-- url     : https://prove2.me/theorems/40163b19-bc90-5ebf-9fca-c877500e2d63
-- title:
--   Sqrt6 Kissing Bound: integral const mul sub pow
-- statement:
--   Integral of a power of a line vanishing at the right endpoint.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/LinearProfileIntegral.lean#L34-L50
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/LinearProfileIntegral.lean#L34-L50

import Mathlib
import Definitions.Def_Sqrt6KissingBound_LinearProfileIntegral
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set
open scoped Interval Real
open intervalIntegral

theorem Sqrt6KissingBound.integral_const_mul_sub_pow (m : ℕ) {a b c : ℝ} :
    (∫ t in a..b, (c * (b - t)) ^ m) =
      c ^ m * (b - a) ^ (m + 1) / (m + 1) := by sorry
