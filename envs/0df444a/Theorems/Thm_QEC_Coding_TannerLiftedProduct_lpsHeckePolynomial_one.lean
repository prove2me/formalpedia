-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:29:07.533625+00:00
-- url     : https://prove2.me/theorems/cfaf755a-ee99-4a76-afb5-4e0fe2affd8a
-- title:
--   Tanner Lifted Product: lps Hecke Polynomial one
-- statement:
--   The Tanner Lifted Product construction uses the lps Hecke Polynomial one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L30-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L30-L33

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
    (R : Type*) [CommRing R] (p : R) :
    lpsHeckePolynomial R p 1 = X := by sorry
