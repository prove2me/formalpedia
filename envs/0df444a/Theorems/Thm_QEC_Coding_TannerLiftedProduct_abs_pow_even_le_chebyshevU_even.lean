-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_pow_even_le_chebyshevU_even
-- name    : QEC.Coding.TannerLiftedProduct.abs_pow_even_le_chebyshevU_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:46:34.045699+00:00
-- url     : https://prove2.me/theorems/432fe5fc-3260-48b4-b602-6101cc06c97a
-- title:
--   Tanner Lifted Product: abs pow even le chebyshev U even
-- statement:
--   Outside `[-1,1]`, an even Chebyshev `U` value dominates the
--   corresponding even power of the absolute value.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L403-L414
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L403-L414

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem QEC.Coding.TannerLiftedProduct.abs_pow_even_le_chebyshevU_even
    (x : ℝ) (n : ℕ) (hx : 1 ≤ |x|) :
    |x| ^ (2 * n) ≤
      (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x := by sorry
