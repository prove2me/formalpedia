-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_add_two
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_add_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:29:37.395362+00:00
-- url     : https://prove2.me/theorems/227dc7d2-af90-45c8-b9dc-6d64e306c46e
-- title:
--   Tanner Lifted Product: lps Hecke Polynomial eval add two
-- statement:
--   Scalar evaluation satisfies the same Hecke recurrence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L54-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L54-L60

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_add_two
    (R : Type*) [CommRing R] (p x : R) (n : ℕ) :
    (lpsHeckePolynomial R p (n + 2)).eval x =
      x * (lpsHeckePolynomial R p (n + 1)).eval x -
        p * (lpsHeckePolynomial R p n).eval x := by sorry
