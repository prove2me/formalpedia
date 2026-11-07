-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_chebyshevU_even_le_odd
-- name    : QEC.Coding.TannerLiftedProduct.abs_chebyshevU_even_le_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:30:16.163791+00:00
-- url     : https://prove2.me/theorems/0d1a815d-a156-4bdd-941e-dfd020b480e6
-- title:
--   Tanner Lifted Product: abs chebyshev U even le odd
-- statement:
--   On the Ramanujan interval, the even Chebyshev polynomial has its
--   standard linear bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L298-L319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L298-L319

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem QEC.Coding.TannerLiftedProduct.abs_chebyshevU_even_le_odd
    (x : ℝ) (hx : |x| ≤ 1) (n : ℕ) :
    |(Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x| ≤
      ((2 * n + 1 : ℕ) : ℝ) := by sorry
