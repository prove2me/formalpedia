-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_measure_groupedLightBadAt_le_pow
-- name    : QEC.Coding.FiberBundle.RandomPartition.measure_groupedLightBadAt_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:24:10.52221+00:00
-- url     : https://prove2.me/theorems/72528f75-7b78-4d1a-939e-b4bbf9cc85dd
-- title:
--   Random Partition: measure grouped Light Bad At le pow
-- statement:
--   Fixed-index bound in geometric-weight form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1857-L1896
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1857-L1896

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

theorem QEC.Coding.FiberBundle.RandomPartition.measure_groupedLightBadAt_le_pow
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (index : LightFailureIndex r typeCount) :
    (distribution r Delta (by omega)).toMeasure.real
        (groupedLightBadAt r Delta typeCount index) ≤
      (Real.exp
        (-(Delta : Real) / (200 * typeCount))) ^
          (HammingWeight index.2.1.1 +
            HammingWeight index.2.1.2) := by sorry
