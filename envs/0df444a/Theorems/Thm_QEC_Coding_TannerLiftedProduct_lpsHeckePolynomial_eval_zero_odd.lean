-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:29:29.611503+00:00
-- url     : https://prove2.me/theorems/2ba65fc2-31fd-48a7-b58c-d06dc7467dcc
-- title:
--   Tanner Lifted Product: lps Hecke Polynomial eval zero odd
-- statement:
--   The Tanner Lifted Product construction uses the lps Hecke Polynomial eval zero odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L86-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L86-L89

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
    (R : Type*) [CommRing R] (p : R) (n : ℕ) :
    (lpsHeckePolynomial R p (2 * n + 1)).eval 0 = 0 := by sorry
