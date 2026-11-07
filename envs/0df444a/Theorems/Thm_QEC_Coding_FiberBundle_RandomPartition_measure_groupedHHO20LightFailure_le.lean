-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_measure_groupedHHO20LightFailure_le
-- name    : QEC.Coding.FiberBundle.RandomPartition.measure_groupedHHO20LightFailure_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:19:44.514481+00:00
-- url     : https://prove2.me/theorems/4e8bd63e-472f-43d2-9050-5c109c9807f3
-- title:
--   Random Partition: measure grouped HHO20 Light Failure le
-- statement:
--   Simultaneous light-check failure mass, before discharging the final
--   numeric geometric-series inequality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1914-L1953
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1914-L1953

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

theorem QEC.Coding.FiberBundle.RandomPartition.measure_groupedHHO20LightFailure_le
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r) :
    (distribution r Delta (by omega)).toMeasure.real
        {sample | ¬ HasGroupedHHO20LightChecks
          (r := r) (typeCount := typeCount) Delta sample} ≤
      typeCount *
        ((1 +
          Real.exp
            (-(Delta : Real) / (200 * typeCount))) ^
              (8 * r) - 1) := by sorry
