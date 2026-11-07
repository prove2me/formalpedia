-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_even_lower_bound
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_even_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:46:25.745206+00:00
-- url     : https://prove2.me/theorems/9c37f0a1-4c28-4e00-b0fa-defa85b570f5
-- title:
--   Tanner Lifted Product: lps Hecke Polynomial eval even lower bound
-- statement:
--   Coordinate-free version of the even Hecke lower bound.  For positive
--   `p`, every real evaluation is at least `-(2n+1)pⁿ`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L284-L294
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L284-L294

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_even_lower_bound
    {p : ℝ} (hp : 0 < p) (x : ℝ) (n : ℕ) :
    -((2 * n + 1 : ℕ) : ℝ) * p ^ n ≤
      (lpsHeckePolynomial ℝ p (2 * n)).eval x := by sorry
