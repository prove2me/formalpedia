-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even_odd
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:29:46.61223+00:00
-- url     : https://prove2.me/theorems/ee3389a9-bd64-4bc9-8da3-1df69fae5d74
-- title:
--   Tanner Lifted Product: lps Hecke Polynomial eval zero even odd
-- statement:
--   The constant terms of the even and odd LPS Hecke polynomials.  This is
--   the elementary correction term which appears when the constant graph mode
--   is removed from the exact LPS trace formula.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L65-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L65-L79

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even_odd
    (R : Type*) [CommRing R] (p : R) (n : ℕ) :
    (lpsHeckePolynomial R p (2 * n)).eval 0 = (-p) ^ n ∧
      (lpsHeckePolynomial R p (2 * n + 1)).eval 0 = 0 := by sorry
