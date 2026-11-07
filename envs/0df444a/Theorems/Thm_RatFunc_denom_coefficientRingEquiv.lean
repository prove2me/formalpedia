-- Prove2me | Theorems.Thm_RatFunc_denom_coefficientRingEquiv
-- name    : RatFunc.denom_coefficientRingEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:54:00.929323+00:00
-- url     : https://prove2.me/theorems/f7e025d8-f576-4de7-b372-2836393471bc
-- title:
--   Rat Func: denom coefficient Ring Equiv
-- statement:
--   Normalized denominators are transported coefficientwise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/RatFuncCoefficientEquiv.lean#L57-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/RatFuncCoefficientEquiv.lean#L57-L84

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_RatFuncCoefficientEquiv
set_option autoImplicit false
open RatFunc

theorem RatFunc.denom_coefficientRingEquiv
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (x : RatFunc K) :
    (coefficientRingEquiv e x).denom =
      x.denom.map e.toRingHom := by sorry
