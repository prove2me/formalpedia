-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_log_const_mul_s_sq_mul_two_pow_sq_lt
-- name    : QEC.Coding.FiberBundle.RandomPartition.log_const_mul_s_sq_mul_two_pow_sq_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:52:45.339087+00:00
-- url     : https://prove2.me/theorems/af71b6b7-3908-42b3-830f-d8ace109011c
-- title:
--   Random Partition: log const mul s sq mul two pow sq lt
-- statement:
--   Variant with the two polynomial factors needed by the light-check union
--   bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L456-L501
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L456-L501

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition

theorem QEC.Coding.FiberBundle.RandomPartition.log_const_mul_s_sq_mul_two_pow_sq_lt
    (coefficient s : Nat)
    (hCoefficient : 0 < coefficient)
    (hCoefficientSmall : coefficient < 2 ^ 100)
    (hs : 20 ≤ s) :
    Real.log
        (coefficient * s ^ 2 * (2 ^ s) ^ 2 : Nat) <
      9 * (s : Real) := by sorry
