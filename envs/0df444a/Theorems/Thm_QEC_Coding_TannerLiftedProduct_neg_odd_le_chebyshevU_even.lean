-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_neg_odd_le_chebyshevU_even
-- name    : QEC.Coding.TannerLiftedProduct.neg_odd_le_chebyshevU_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:29:57.690298+00:00
-- url     : https://prove2.me/theorems/9c51406e-cbd2-47b4-b481-3c8447d74f20
-- title:
--   Tanner Lifted Product: neg odd le chebyshev U even
-- statement:
--   Uniform lower bound for even Chebyshev polynomials of the second kind.
--   This is the cancellation-control estimate needed by the finite trace method.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L247-L269
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L247-L269

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem QEC.Coding.TannerLiftedProduct.neg_odd_le_chebyshevU_even (x : ℝ) : ∀ n : ℕ,
    -((2 * n + 1 : ℕ) : ℝ) ≤
      (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x
  := by sorry
