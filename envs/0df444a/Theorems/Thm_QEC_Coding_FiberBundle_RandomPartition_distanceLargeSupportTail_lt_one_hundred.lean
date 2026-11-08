-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_distanceLargeSupportTail_lt_one_hundred
-- name    : QEC.Coding.FiberBundle.RandomPartition.distanceLargeSupportTail_lt_one_hundred
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:53:32.127218+00:00
-- url     : https://prove2.me/theorems/983367e7-b9e2-4cc5-b26b-6704c756de21
-- title:
--   Random Partition: distance Large Support Tail lt one hundred
-- statement:
--   When `r` is a multiple of five, the large-support distance tail groups
--   into powers of a single rational number strictly below `9/10`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L83-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L83-L107

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition

theorem QEC.Coding.FiberBundle.RandomPartition.distanceLargeSupportTail_lt_one_hundred
    (r : Nat) (hr : 500 ≤ r) (hFive : 5 ∣ r) :
    ((3 : Real) ^ ((4 * r) / 5) *
        ((4 : Real) / 3) ^ (4 * r)) *
        ((172 : Real) / 343) ^ (3 * r) <
      1 / 100 := by sorry
