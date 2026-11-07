-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_measure_groupedHHO20ConstructionBaseFailure_le
-- name    : QEC.Coding.FiberBundle.RandomPartition.measure_groupedHHO20ConstructionBaseFailure_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:26:42.115374+00:00
-- url     : https://prove2.me/theorems/2b6b0797-7ad8-417c-bd49-ddf48e6a8241
-- title:
--   Random Partition: measure grouped HHO20 Construction Base Failure le
-- statement:
--   Failure mass for the entire random base layer: rank, classical distance,
--   degree windows, strong small-set expansion, and both partitioned-check
--   events.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L4104-L4164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L4104-L4164

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

theorem QEC.Coding.FiberBundle.RandomPartition.measure_groupedHHO20ConstructionBaseFailure_le
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hDelta : 0 < Delta) (hDeltaOne : 1 ≤ Delta)
    (hTypeSmall : (100 : Real) * typeCount ≤ r)
    (hHeavyScale :
      (100 : Real) * typeCount *
          (1 + 2 * Real.log Delta) ≤
        Delta)
    (typeShifts : Fin typeCount → Fin (ell - 1)) :
    (distribution r Delta (by omega)).toMeasure.real
        {sample |
          ¬HasGroupedHHO20ConstructionBase
            Delta typeShifts sample} ≤
      (fullyGoodBaseFailureBound r Delta).toReal +
        ((typeCount : Real) *
            ((1 +
              Real.exp
                (-(Delta : Real) / (200 * typeCount))) ^
                  (8 * r) - 1) +
          Real.exp (-(r : Real) / 10)) := by sorry
