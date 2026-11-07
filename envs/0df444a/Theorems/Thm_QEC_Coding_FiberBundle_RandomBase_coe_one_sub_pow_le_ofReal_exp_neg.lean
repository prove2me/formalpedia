-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_coe_one_sub_pow_le_ofReal_exp_neg
-- name    : QEC.Coding.FiberBundle.RandomBase.coe_one_sub_pow_le_ofReal_exp_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:52:29.619505+00:00
-- url     : https://prove2.me/theorems/7cdbdf76-e48e-4f51-9b76-350e00319b8b
-- title:
--   Random Base: coe one sub pow le of Real exp neg
-- statement:
--   The elementary finite-power exponential envelope `(1 - x)^n ≤ exp(-nx)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L295-L319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L295-L319

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.coe_one_sub_pow_le_ofReal_exp_neg
    (x : NNReal) (hx : x ≤ 1) (n : Nat) :
    (((1 - x : NNReal) : ENNReal) ^ n) ≤
      ENNReal.ofReal (Real.exp (-(n : Real) * (x : Real))) := by sorry
