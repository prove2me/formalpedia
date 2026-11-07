-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_neg_one_le_chebyshevT_even
-- name    : QEC.Coding.TannerLiftedProduct.neg_one_le_chebyshevT_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:30:01.903205+00:00
-- url     : https://prove2.me/theorems/1bd71f76-783a-4a68-afea-54954be5b31e
-- title:
--   Tanner Lifted Product: neg one le chebyshev T even
-- statement:
--   Every even Chebyshev polynomial of the first kind is bounded below by
--   `-1` on the whole real line.  Inside `[-1,1]` this is the usual Chebyshev
--   bound; outside it follows from the hyperbolic branch and even parity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L224-L243
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L224-L243

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem QEC.Coding.TannerLiftedProduct.neg_one_le_chebyshevT_even (x : ℝ) (n : ℕ) :
    -1 ≤ (Polynomial.Chebyshev.T ℝ (2 * (n : ℤ))).eval x := by sorry
