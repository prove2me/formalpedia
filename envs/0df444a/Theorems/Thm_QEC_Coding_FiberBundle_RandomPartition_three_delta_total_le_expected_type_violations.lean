-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_three_delta_total_le_expected_type_violations
-- name    : QEC.Coding.FiberBundle.RandomPartition.three_delta_total_le_expected_type_violations
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:23:28.314007+00:00
-- url     : https://prove2.me/theorems/cd9d9edd-a373-4b97-bc37-ac55fc1136e9
-- title:
--   Random Partition: three delta total le expected type violations
-- statement:
--   The exact type-fiber size and the `.04 p t` row bound give expected
--   type violations at least `.03 Delta t / typeCount`, in integer-cleared
--   form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1539-L1599
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1539-L1599

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

theorem QEC.Coding.FiberBundle.RandomPartition.three_delta_total_le_expected_type_violations
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (τ : Fin typeCount)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (hy : Delta * HammingWeight y ≤ 4 * (4 * r))
    (hz : Delta * HammingWeight z ≤ 4 * (4 * r)) :
    3 * (Delta : Real) *
          ((HammingWeight y : Real) + HammingWeight z) ≤
      100 * typeCount *
        ((rowDistribution r Delta (by omega)).toMeasure.real
            {row | rowPairSyndrome row y z ≠ 0} *
          (typeRows r typeCount τ).card) := by sorry
