-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_add_two
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_add_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:29:42.815498+00:00
-- url     : https://prove2.me/theorems/b23121a8-c913-4771-a927-6705361b8a48
-- title:
--   Tanner Lifted Product: lps Hecke Polynomial add two
-- statement:
--   The exact recurrence stated in the LPS trace proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L36-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L36-L41

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_add_two
    (R : Type*) [CommRing R] (p : R) (n : ℕ) :
    lpsHeckePolynomial R p (n + 2) =
      X * lpsHeckePolynomial R p (n + 1) -
        C p * lpsHeckePolynomial R p n := by sorry
