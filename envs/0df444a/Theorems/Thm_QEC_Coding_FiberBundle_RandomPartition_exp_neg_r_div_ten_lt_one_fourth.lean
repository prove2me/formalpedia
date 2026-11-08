-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_exp_neg_r_div_ten_lt_one_fourth
-- name    : QEC.Coding.FiberBundle.RandomPartition.exp_neg_r_div_ten_lt_one_fourth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:53:37.409914+00:00
-- url     : https://prove2.me/theorems/257a2b57-d994-43b9-8534-840118751775
-- title:
--   Random Partition: exp neg r div ten lt one fourth
-- statement:
--   At every base scale used below, the heavy-check failure budget is already
--   below one quarter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L230-L247
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L230-L247

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition

theorem QEC.Coding.FiberBundle.RandomPartition.exp_neg_r_div_ten_lt_one_fourth
    (r : Nat) (hr : 20 ≤ r) :
    Real.exp (-(r : Real) / 10) < (1 : Real) / 4 := by sorry
