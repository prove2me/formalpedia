-- Prove2me | Theorems.Thm_RatFunc_coefficientRingEquiv_apply_div
-- name    : RatFunc.coefficientRingEquiv_apply_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:54:00.797484+00:00
-- url     : https://prove2.me/theorems/b10cb4d3-da59-47bd-8d49-6443fac91b55
-- title:
--   Rat Func: coefficient Ring Equiv apply div
-- statement:
--   The Rat Func construction uses the coefficient Ring Equiv apply div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/RatFuncCoefficientEquiv.lean#L39-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Algebra/RatFuncCoefficientEquiv.lean#L39-L54

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_RatFuncCoefficientEquiv
set_option autoImplicit false
open RatFunc

theorem RatFunc.coefficientRingEquiv_apply_div
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (p q : Polynomial K) :
    coefficientRingEquiv e
        (algebraMap (Polynomial K) (RatFunc K) p /
          algebraMap (Polynomial K) (RatFunc K) q) =
      algebraMap (Polynomial L) (RatFunc L) (Polynomial.mapEquiv e p) /
        algebraMap (Polynomial L) (RatFunc L) (Polynomial.mapEquiv e q) := by sorry
