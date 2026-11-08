-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_fullyGoodBaseFailureBound_toReal
-- name    : QEC.Coding.FiberBundle.RandomPartition.fullyGoodBaseFailureBound_toReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:52:29.932901+00:00
-- url     : https://prove2.me/theorems/3bc6ab2f-9eb0-4b11-92bf-862cc225241a
-- title:
--   Random Partition: fully Good Base Failure Bound to Real
-- statement:
--   The ENNReal union bound contains no hidden infinite contribution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L27-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L27-L60

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition

theorem QEC.Coding.FiberBundle.RandomPartition.fullyGoodBaseFailureBound_toReal
    (r Delta : Nat) :
    (fullyGoodBaseFailureBound r Delta).toReal =
      fullyGoodBaseFailureBoundReal r Delta := by sorry
