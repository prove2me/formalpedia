-- Prove2me | Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_polynomial_eval__mul_eq_eval_zero_smul_49a5ce81d920
-- name    : P2M_QEC_Coding_TannerLiftedProduct_polynomial_eval__mul_eq_eval_zero_smul_49a5ce81d920
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:46:16.224659+00:00
-- url     : https://prove2.me/theorems/1e385ab6-f16c-43d7-935c-e049f9f7d0c8
-- title:
--   P2 M QEC Coding Tanner Lifted Product polynomial eval  mul eq eval zero smul 49a5ce81d920: P2 M QEC Coding Tanner Lifted Product polynomial eval  mul eq eval zero smul 49a5ce81d920
-- statement:
--   Evaluating a polynomial at an element which kills `e` on the right and
--   then multiplying by `e` retains only the constant coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L109-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L109-L122

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem P2M_QEC_Coding_TannerLiftedProduct_polynomial_eval__mul_eq_eval_zero_smul_49a5ce81d920
    {A : Type*} [Ring A] [Algebra ℂ A]
    (P : ℂ[X]) (x e : A) (hxe : x * e = 0) :
    P.eval₂ (algebraMap ℂ A) x * e = P.eval 0 • e := by sorry

alias «QEC».«Coding».«TannerLiftedProduct».«polynomial_eval₂_mul_eq_eval_zero_smul» := P2M_QEC_Coding_TannerLiftedProduct_polynomial_eval__mul_eq_eval_zero_smul_49a5ce81d920
