-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:29:04.933545+00:00
-- url     : https://prove2.me/theorems/e655e336-1ef7-4d96-8eac-18c50fe998bf
-- title:
--   Tanner Lifted Product: lps Hecke Polynomial zero
-- statement:
--   The Tanner Lifted Product construction uses the lps Hecke Polynomial zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L24-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L24-L28

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
    (R : Type*) [CommRing R] (p : R) :
    lpsHeckePolynomial R p 0 = 1 := by sorry
