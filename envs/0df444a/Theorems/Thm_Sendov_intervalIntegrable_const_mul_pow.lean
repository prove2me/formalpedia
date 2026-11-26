-- Prove2me | Theorems.Thm_Sendov_intervalIntegrable_const_mul_pow
-- name    : Sendov.intervalIntegrable_const_mul_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:54:01.347885+00:00
-- url     : https://prove2.me/theorems/db911e78-dd07-5ea1-9d13-b9f2b08fcd1c
-- title:
--   Sendov: interval Integrable const mul pow
-- statement:
--   Every monomial is interval integrable on `[0,1]`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Moments.lean#L38-L40
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Moments.lean#L38-L40

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Moments
set_option autoImplicit false
open Sendov
open MeasureTheory Finset

theorem Sendov.intervalIntegrable_const_mul_pow (a : ℝ) (m : ℕ) :
    IntervalIntegrable (fun t : ℝ => a * t ^ m) volume 0 1 := by sorry
