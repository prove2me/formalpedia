-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:29:11.206207+00:00
-- url     : https://prove2.me/theorems/146c4a69-9480-475c-a9cc-7d110f99cf37
-- title:
--   Tanner Lifted Product: lps Hecke Polynomial eval one
-- statement:
--   The Tanner Lifted Product construction uses the lps Hecke Polynomial eval one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L48-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L48-L51

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
    (R : Type*) [CommRing R] (p x : R) :
    (lpsHeckePolynomial R p 1).eval x = x := by sorry
