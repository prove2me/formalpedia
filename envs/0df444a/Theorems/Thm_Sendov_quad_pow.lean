-- Prove2me | Theorems.Thm_Sendov_quad_pow
-- name    : Sendov.quad_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:54:00.259803+00:00
-- url     : https://prove2.me/theorems/3c46d056-81de-5002-b275-95979a73d9f7
-- title:
--   Sendov: quad pow
-- statement:
--   The binomial expansion of a power of a quadratic.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Moments.lean#L43-L58
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Moments.lean#L43-L58

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Moments
set_option autoImplicit false
open Sendov
open MeasureTheory Finset

theorem Sendov.quad_pow (b d t : ℝ) (k : ℕ) :
    (1 + b * t + d * t ^ 2) ^ k
      = ∑ i ∈ range (k + 1), ∑ l ∈ range (i + 1),
          ((k.choose i : ℝ) * (i.choose l) * b ^ l * d ^ (i - l)) * t ^ (2 * i - l) := by sorry
