-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_measure_groupedLightFailure_le
-- name    : QEC.Coding.FiberBundle.RandomPartition.measure_groupedLightFailure_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:23:26.288763+00:00
-- url     : https://prove2.me/theorems/6e06028b-8524-41e2-8084-6e352373d370
-- title:
--   Random Partition: measure grouped Light Failure le
-- statement:
--   Fixed-type, fixed-word light-check failure probability.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1602-L1685
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1602-L1685

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

theorem QEC.Coding.FiberBundle.RandomPartition.measure_groupedLightFailure_le
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (τ : Fin typeCount)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (hy : Delta * HammingWeight y ≤ 4 * (4 * r))
    (hz : Delta * HammingWeight z ≤ 4 * (4 * r)) :
    (distribution r Delta (by omega)).toMeasure.real
        {sample |
          100 * typeCount *
              groupedTypeViolationCount sample τ y z <
            Delta * (HammingWeight y + HammingWeight z)} ≤
      Real.exp
        (-((Delta : Real) *
            ((HammingWeight y : Real) + HammingWeight z)) /
          (200 * typeCount)) := by sorry
