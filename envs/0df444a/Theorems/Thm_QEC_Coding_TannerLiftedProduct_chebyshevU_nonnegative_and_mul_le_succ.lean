-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_chebyshevU_nonnegative_and_mul_le_succ
-- name    : QEC.Coding.TannerLiftedProduct.chebyshevU_nonnegative_and_mul_le_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:30:15.998472+00:00
-- url     : https://prove2.me/theorems/c16c7a13-5beb-4e56-b596-a888ee7f7ff4
-- title:
--   Tanner Lifted Product: chebyshev U nonnegative and mul le succ
-- statement:
--   On `[1,∞)`, consecutive Chebyshev `U` values are nonnegative and grow
--   by at least a factor of the evaluation point.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L349-L384
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L349-L384

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem QEC.Coding.TannerLiftedProduct.chebyshevU_nonnegative_and_mul_le_succ
    {x : ℝ} (hx : 1 ≤ x) : ∀ n : ℕ,
    0 ≤ (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x ∧
      x * (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x ≤
        (Polynomial.Chebyshev.U ℝ ((n + 1 : ℕ) : ℤ)).eval x
  := by sorry
