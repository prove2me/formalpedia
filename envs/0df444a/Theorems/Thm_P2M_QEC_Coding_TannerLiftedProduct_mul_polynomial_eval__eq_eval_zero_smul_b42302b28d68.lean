-- Prove2me | Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_mul_polynomial_eval__eq_eval_zero_smul_b42302b28d68
-- name    : P2M_QEC_Coding_TannerLiftedProduct_mul_polynomial_eval__eq_eval_zero_smul_b42302b28d68
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:29:58.310197+00:00
-- url     : https://prove2.me/theorems/c4c53236-6575-4a3c-b565-9b773e6933dc
-- title:
--   P2 M QEC Coding Tanner Lifted Product mul polynomial eval  eq eval zero smul b42302b28d68: P2 M QEC Coding Tanner Lifted Product mul polynomial eval  eq eval zero smul b42302b28d68
-- statement:
--   Left-handed form of `polynomial_eval₂_mul_eq_eval_zero_smul`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L125-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L125-L146

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem P2M_QEC_Coding_TannerLiftedProduct_mul_polynomial_eval__eq_eval_zero_smul_b42302b28d68
    {A : Type*} [Ring A] [Algebra ℂ A]
    (P : ℂ[X]) (x e : A) (hex : e * x = 0) :
    e * P.eval₂ (algebraMap ℂ A) x = P.eval 0 • e := by sorry

alias «QEC».«Coding».«TannerLiftedProduct».«mul_polynomial_eval₂_eq_eval_zero_smul» := P2M_QEC_Coding_TannerLiftedProduct_mul_polynomial_eval__eq_eval_zero_smul_b42302b28d68
