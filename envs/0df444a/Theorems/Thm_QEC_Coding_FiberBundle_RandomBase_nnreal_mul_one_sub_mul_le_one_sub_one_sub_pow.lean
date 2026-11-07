-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_nnreal_mul_one_sub_mul_le_one_sub_one_sub_pow
-- name    : QEC.Coding.FiberBundle.RandomBase.nnreal_mul_one_sub_mul_le_one_sub_one_sub_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:52:22.399365+00:00
-- url     : https://prove2.me/theorems/e7b230d1-f4fd-4661-a10e-e9020f9397a8
-- title:
--   Random Base: nnreal mul one sub mul le one sub one sub pow
-- statement:
--   A second-order lower bound for a Bernoulli union.  Unlike an asymptotic
--   Taylor estimate, this holds for every finite `n` and every `p ≤ 1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L233-L292
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L233-L292

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.nnreal_mul_one_sub_mul_le_one_sub_one_sub_pow
    (p : NNReal) (hp : p ≤ 1) (n : Nat) :
    (n : NNReal) * p * (1 - (n : NNReal) * p) ≤
      1 - (1 - p : NNReal) ^ n := by sorry
