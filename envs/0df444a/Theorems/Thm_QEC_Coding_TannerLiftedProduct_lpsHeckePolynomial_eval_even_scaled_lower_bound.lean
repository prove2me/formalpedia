-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_even_scaled_lower_bound
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_even_scaled_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:30:09.991311+00:00
-- url     : https://prove2.me/theorems/5e45ab42-7a67-456a-ba16-aeb4b0af06bb
-- title:
--   Tanner Lifted Product: lps Hecke Polynomial eval even scaled lower bound
-- statement:
--   Scaled cancellation-control bound for the even LPS Hecke polynomials.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L272-L280
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L272-L280

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_even_scaled_lower_bound
    {p : ℝ} (hp : 0 ≤ p) (x : ℝ) (n : ℕ) :
    -((2 * n + 1 : ℕ) : ℝ) * Real.sqrt p ^ (2 * n) ≤
      (lpsHeckePolynomial ℝ p (2 * n)).eval
        (2 * Real.sqrt p * x) := by sorry
