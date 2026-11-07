-- Prove2me | Theorems.Thm_RatFunc_coefficientRingEquiv_X
-- name    : RatFunc.coefficientRingEquiv_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:30:47.827219+00:00
-- url     : https://prove2.me/theorems/4476506f-e078-498c-9156-138296d0b557
-- title:
--   Rat Func: coefficient Ring Equiv X
-- statement:
--   The Rat Func construction uses the coefficient Ring Equiv X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/RatFuncCoefficientEquiv.lean#L114-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/RatFuncCoefficientEquiv.lean#L114-L120

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_RatFuncCoefficientEquiv
set_option autoImplicit false
open RatFunc

theorem RatFunc.coefficientRingEquiv_X
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L) :
    coefficientRingEquiv e (RatFunc.X : RatFunc K) = RatFunc.X := by sorry
