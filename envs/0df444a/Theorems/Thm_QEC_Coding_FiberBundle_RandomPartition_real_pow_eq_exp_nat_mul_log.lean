-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_real_pow_eq_exp_nat_mul_log
-- name    : QEC.Coding.FiberBundle.RandomPartition.real_pow_eq_exp_nat_mul_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:20:32.587286+00:00
-- url     : https://prove2.me/theorems/f06aab5e-6d6c-4d19-b2c9-b9c5f2f8bf99
-- title:
--   Random Partition: real pow eq exp nat mul log
-- statement:
--   A positive real power written as an exponential with a natural
--   multiplier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3571-L3578
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3571-L3578

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomPartition.real_pow_eq_exp_nat_mul_log
    (x : Real) (n : Nat) (hx : 0 < x) :
    x ^ n = Real.exp ((n : Real) * Real.log x) := by sorry
