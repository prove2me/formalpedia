-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowViolation_measureReal_ge_linear_of_light
-- name    : QEC.Coding.FiberBundle.RandomPartition.rowViolation_measureReal_ge_linear_of_light
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:22:33.465763+00:00
-- url     : https://prove2.me/theorems/4cc335d3-82bf-45ad-bbb3-28f87539b91a
-- title:
--   Random Partition: row Violation measure Real ge linear of light
-- statement:
--   The two individual HHO20 light-word cutoffs imply the linear one-row
--   violation bound with no additional probabilistic assumption.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1052-L1067
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1052-L1067

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

theorem QEC.Coding.FiberBundle.RandomPartition.rowViolation_measureReal_ge_linear_of_light
    (r Delta : Nat) (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (hy : Delta * HammingWeight y ≤ 4 * (4 * r))
    (hz : Delta * HammingWeight z ≤ 4 * (4 * r)) :
    (RandomBase.incidenceProbability (4 * r) Delta).toReal *
          ((HammingWeight y : Real) + HammingWeight z) / 25 ≤
      (rowDistribution r Delta (by omega)).toMeasure.real
        {row | rowPairSyndrome row y z ≠ 0} := by sorry
