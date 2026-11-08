-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_fullyGoodBaseFailureBound_toReal_lt_one_tenth
-- name    : QEC.Coding.FiberBundle.RandomPartition.fullyGoodBaseFailureBound_toReal_lt_one_tenth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:53:28.88607+00:00
-- url     : https://prove2.me/theorems/e36e165a-8cb4-4bba-b386-4a5689782d9d
-- title:
--   Random Partition: fully Good Base Failure Bound to Real lt one tenth
-- statement:
--   ENNReal-free corollary for the bound consumed by the sample-selection
--   theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L207-L226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L207-L226

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition

theorem QEC.Coding.FiberBundle.RandomPartition.fullyGoodBaseFailureBound_toReal_lt_one_tenth
    (r Delta : Nat)
    (hr : 500 ≤ r) (hFive : 5 ∣ r)
    (hDegree :
      (14 * r : Real) * Real.exp (-(Delta : Real) / 40000) <
        1 / 100)
    (hRank :
      (3 * r : Real) * Real.exp (-(Delta : Real) / 2) <
        1 / 200)
    (hDistance :
      (4 * r : Real) *
          Real.exp (-(3 : Real) * Delta / 28) <
        1 / 200)
    (hExpansion :
      (3 * r : Real) * Real.exp (-(Delta : Real) / 1000) <
        1 / 200) :
    (fullyGoodBaseFailureBound r Delta).toReal < 1 / 10 := by sorry
