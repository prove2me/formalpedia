-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hho20_joint_failure_sum_lt_one
-- name    : QEC.Coding.FiberBundle.RandomPartition.hho20_joint_failure_sum_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:53:16.068039+00:00
-- url     : https://prove2.me/theorems/0a4f87df-7325-49e1-aa24-563f87ee1bba
-- title:
--   Random Partition: hho20 joint failure sum lt one
-- statement:
--   The paper-natural logarithmic light scale, the four random-base decay
--   loads, and `r ≥ 500` imply the exact numeric inequality required for joint
--   sample selection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L252-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L252-L291

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition

theorem QEC.Coding.FiberBundle.RandomPartition.hho20_joint_failure_sum_lt_one
    (r Delta typeCount : Nat) [NeZero typeCount]
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
        1 / 200)
    (hLightLogScale :
      200 * (typeCount : Real) *
          Real.log (32 * r * typeCount : Nat) <
        Delta) :
    (fullyGoodBaseFailureBound r Delta).toReal +
        ((typeCount : Real) *
            ((1 +
              Real.exp
                (-(Delta : Real) / (200 * typeCount))) ^
                  (8 * r) - 1) +
          Real.exp (-(r : Real) / 10)) <
      1 := by sorry
