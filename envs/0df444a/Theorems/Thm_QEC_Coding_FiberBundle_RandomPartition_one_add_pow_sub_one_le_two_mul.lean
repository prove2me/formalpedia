-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_one_add_pow_sub_one_le_two_mul
-- name    : QEC.Coding.FiberBundle.RandomPartition.one_add_pow_sub_one_le_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:52:59.972978+00:00
-- url     : https://prove2.me/theorems/3d1b9a44-bd9d-45fd-bf03-acdb75f9a646
-- title:
--   Random Partition: one add pow sub one le two mul
-- statement:
--   A finite power of `1 + x` is linear to within a factor two whenever its
--   total exponent load is at most one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L111-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L111-L133

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition

theorem QEC.Coding.FiberBundle.RandomPartition.one_add_pow_sub_one_le_two_mul
    (x : Real) (n : Nat) (hx : 0 ≤ x)
    (hSmall : (n : Real) * x ≤ 1) :
    (1 + x) ^ n - 1 ≤ 2 * ((n : Real) * x) := by sorry
