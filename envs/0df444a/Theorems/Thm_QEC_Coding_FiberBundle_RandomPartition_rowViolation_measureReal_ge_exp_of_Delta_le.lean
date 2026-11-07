-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowViolation_measureReal_ge_exp_of_Delta_le
-- name    : QEC.Coding.FiberBundle.RandomPartition.rowViolation_measureReal_ge_exp_of_Delta_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:22:41.564349+00:00
-- url     : https://prove2.me/theorems/4c2673fb-362f-4676-bd4b-7ecffb7f787a
-- title:
--   Random Partition: row Violation measure Real ge exp of Delta le
-- statement:
--   Assumption-free-in-use form of `prop:chi`: the natural HHO20 scale
--   condition discharges the analytic density side condition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L990-L1000
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L990-L1000

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

theorem QEC.Coding.FiberBundle.RandomPartition.rowViolation_measureReal_ge_exp_of_Delta_le
    (r Delta : Nat) (hDeltaHalf : Delta ≤ 2 * r)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    (1 -
      Real.exp
        (-(RandomBase.incidenceProbability (4 * r) Delta).toReal *
          ((HammingWeight y : Real) + HammingWeight z))) / 2 ≤
      (rowDistribution r Delta (by omega)).toMeasure.real
        {row | rowPairSyndrome row y z ≠ 0} := by sorry
