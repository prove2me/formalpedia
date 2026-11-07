-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_measure_groupedHeavyBadAt_le
-- name    : QEC.Coding.FiberBundle.RandomPartition.measure_groupedHeavyBadAt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:25:46.486068+00:00
-- url     : https://prove2.me/theorems/d87c768b-8b3e-4e83-92c9-0f301d257837
-- title:
--   Random Partition: measure grouped Heavy Bad At le
-- statement:
--   Every indexed heavy bad event has the sharp fixed-configuration mass
--   bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3328-L3352
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3328-L3352

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

theorem QEC.Coding.FiberBundle.RandomPartition.measure_groupedHeavyBadAt_le
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (index : HeavyFailureIndex r Delta typeCount) :
    (distribution r Delta (by omega)).toMeasure.real
        (groupedHeavyBadAt
          r Delta typeCount ell typeShifts index) ≤
      Real.exp (-3 * (r : Real)) := by sorry
