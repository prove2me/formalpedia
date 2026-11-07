-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:29:32.895821+00:00
-- url     : https://prove2.me/theorems/ad30c2fc-f23f-4704-9eff-569d4eb221d9
-- title:
--   Tanner Lifted Product: lps Hecke Polynomial eval zero even
-- statement:
--   The Tanner Lifted Product construction uses the lps Hecke Polynomial eval zero even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L81-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L81-L84

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
    (R : Type*) [CommRing R] (p : R) (n : ℕ) :
    (lpsHeckePolynomial R p (2 * n)).eval 0 = (-p) ^ n := by sorry
