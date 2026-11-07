-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_pow_le_chebyshevU_of_one_le
-- name    : QEC.Coding.TannerLiftedProduct.pow_le_chebyshevU_of_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:30:19.862691+00:00
-- url     : https://prove2.me/theorems/3bbb7862-0a3e-45be-846b-c95f51989794
-- title:
--   Tanner Lifted Product: pow le chebyshev U of one le
-- statement:
--   On `[1,∞)`, `Uₙ(x)` dominates the elementary power `xⁿ`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L387-L399
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L387-L399

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem QEC.Coding.TannerLiftedProduct.pow_le_chebyshevU_of_one_le
    {x : ℝ} (hx : 1 ≤ x) : ∀ n : ℕ,
    x ^ n ≤ (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval x
  := by sorry
