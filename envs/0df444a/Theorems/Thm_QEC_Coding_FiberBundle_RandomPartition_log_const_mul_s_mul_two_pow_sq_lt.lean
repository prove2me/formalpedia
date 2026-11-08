-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_log_const_mul_s_mul_two_pow_sq_lt
-- name    : QEC.Coding.FiberBundle.RandomPartition.log_const_mul_s_mul_two_pow_sq_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:52:03.665589+00:00
-- url     : https://prove2.me/theorems/dc7372ea-8423-481f-9b91-06afac0da095
-- title:
--   Random Partition: log const mul s mul two pow sq lt
-- statement:
--   Logarithm of the common `constant * s * 4^s` shape is at most linear in
--   `s`, with a deliberately loose constant that keeps later arithmetic robust.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L408-L452
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L408-L452

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition

theorem QEC.Coding.FiberBundle.RandomPartition.log_const_mul_s_mul_two_pow_sq_lt
    (coefficient s : Nat)
    (hCoefficient : 0 < coefficient)
    (hCoefficientSmall : coefficient < 2 ^ 100)
    (hs : 20 ≤ s) :
    Real.log
        (coefficient * s * (2 ^ s) ^ 2 : Nat) <
      8 * (s : Real) := by sorry
