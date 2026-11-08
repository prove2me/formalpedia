-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rankLargeSupportTail_lt_one_hundred
-- name    : QEC.Coding.FiberBundle.RandomPartition.rankLargeSupportTail_lt_one_hundred
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:52:43.64747+00:00
-- url     : https://prove2.me/theorems/12eef4d6-788b-4443-9121-126469e7bb8a
-- title:
--   Random Partition: rank Large Support Tail lt one hundred
-- statement:
--   The large-support rank tail is already below one percent once the base
--   scale reaches one hundred.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L64-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L64-L79

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition

theorem QEC.Coding.FiberBundle.RandomPartition.rankLargeSupportTail_lt_one_hundred
    (r : Nat) (hr : 100 ≤ r) :
    (2 : Real) ^ (3 * r) *
        ((4 : Real) / 7) ^ (4 * r) <
      1 / 100 := by sorry
