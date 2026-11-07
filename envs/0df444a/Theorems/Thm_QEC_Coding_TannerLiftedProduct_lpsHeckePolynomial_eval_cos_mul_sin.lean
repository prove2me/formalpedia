-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_cos_mul_sin
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_cos_mul_sin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:46:20.373565+00:00
-- url     : https://prove2.me/theorems/9a3a984f-7391-40da-a1c5-3fe6b9c9424a
-- title:
--   Tanner Lifted Product: lps Hecke Polynomial eval cos mul sin
-- statement:
--   Trigonometric form of the scaled Hecke evaluation.  This is the exact
--   finite-dimensional spectral expression used in the LPS trace comparison.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L204-L219
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L204-L219

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_cos_mul_sin
    {p : ℝ} (hp : 0 ≤ p) (theta : ℝ) (n : ℕ) :
    (lpsHeckePolynomial ℝ p n).eval
          (2 * Real.sqrt p * Real.cos theta) * Real.sin theta =
      Real.sqrt p ^ n * Real.sin (((n : ℝ) + 1) * theta) := by sorry
