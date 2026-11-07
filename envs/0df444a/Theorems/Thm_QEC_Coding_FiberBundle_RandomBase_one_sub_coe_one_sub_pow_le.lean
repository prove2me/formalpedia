-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_one_sub_coe_one_sub_pow_le
-- name    : QEC.Coding.FiberBundle.RandomBase.one_sub_coe_one_sub_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:51:50.96322+00:00
-- url     : https://prove2.me/theorems/42c9d194-70f0-4b47-9949-43c06c522c58
-- title:
--   Random Base: one sub coe one sub pow le
-- statement:
--   The probability that at least one of `n` Bernoulli coordinates is hit is at
--   most `n p`.  This is Bernoulli's inequality expressed in the `ENNReal` form
--   used by finite event masses.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L208-L227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L208-L227

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.one_sub_coe_one_sub_pow_le
    (p : NNReal) (hp : p ≤ 1) (n : Nat) :
    1 - (((1 - p : NNReal) : ENNReal) ^ n) ≤
      (n : ENNReal) * (p : ENNReal) := by sorry
