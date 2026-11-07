-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_lpsHeckePolynomial_eval_even_le_of_ramanujan
-- name    : QEC.Coding.TannerLiftedProduct.abs_lpsHeckePolynomial_eval_even_le_of_ramanujan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:46:32.092103+00:00
-- url     : https://prove2.me/theorems/05046850-d587-400e-8faf-626f46f701b8
-- title:
--   Tanner Lifted Product: abs lps Hecke Polynomial eval even le of ramanujan
-- statement:
--   The spectral Ramanujan bound gives the optimal even Hecke evaluation
--   bound, with no asymptotic loss.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L323-L345
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L323-L345

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem QEC.Coding.TannerLiftedProduct.abs_lpsHeckePolynomial_eval_even_le_of_ramanujan
    {p : ℝ} (hp : 0 < p) (x : ℝ)
    (hx : |x| ≤ 2 * Real.sqrt p) (n : ℕ) :
    |(lpsHeckePolynomial ℝ p (2 * n)).eval x| ≤
      ((2 * n + 1 : ℕ) : ℝ) * p ^ n := by sorry
