-- Prove2me | Theorems.Thm_RatFunc_num_coefficientRingEquiv
-- name    : RatFunc.num_coefficientRingEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:30:44.243938+00:00
-- url     : https://prove2.me/theorems/d5241ad7-a05f-4b75-92a1-8ac4e3ef2e8d
-- title:
--   Rat Func: num coefficient Ring Equiv
-- statement:
--   Normalized numerators are transported coefficientwise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/RatFuncCoefficientEquiv.lean#L87-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/RatFuncCoefficientEquiv.lean#L87-L104

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_RatFuncCoefficientEquiv
set_option autoImplicit false
open RatFunc

theorem RatFunc.num_coefficientRingEquiv
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (x : RatFunc K) :
    (coefficientRingEquiv e x).num =
      x.num.map e.toRingHom := by sorry
