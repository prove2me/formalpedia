-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_two_mul_sqrt_mul
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_two_mul_sqrt_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:29:42.49348+00:00
-- url     : https://prove2.me/theorems/49d0dcab-0214-4d10-8e9a-05ef5403ccdd
-- title:
--   Tanner Lifted Product: lps Hecke Polynomial eval two mul sqrt mul
-- statement:
--   After the substitution `x ↦ 2 √p x`, the LPS Hecke polynomials are
--   scaled Chebyshev polynomials of the second kind.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L179-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L179-L200

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_two_mul_sqrt_mul
    {p : ℝ} (hp : 0 ≤ p) (x : ℝ) : ∀ n : ℕ,
    (lpsHeckePolynomial ℝ p n).eval (2 * Real.sqrt p * x) =
      Real.sqrt p ^ n *
        (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x
  := by sorry
