-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowViolation_measureReal_ge_linear
-- name    : QEC.Coding.FiberBundle.RandomPartition.rowViolation_measureReal_ge_linear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:22:44.585837+00:00
-- url     : https://prove2.me/theorems/f4cd336f-a897-4ccb-b9ac-de794f23467b
-- title:
--   Random Partition: row Violation measure Real ge linear
-- statement:
--   Linear `prop:chi` bound on the entire light-word range.  The integer
--   hypothesis is exactly `p (|y|+|z|) ≤ 8` after substituting
--   `p = Delta/(4r)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1005-L1048
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1005-L1048

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

theorem QEC.Coding.FiberBundle.RandomPartition.rowViolation_measureReal_ge_linear
    (r Delta : Nat) (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (hTotal :
      Delta * (HammingWeight y + HammingWeight z) ≤ 32 * r) :
    (RandomBase.incidenceProbability (4 * r) Delta).toReal *
          ((HammingWeight y : Real) + HammingWeight z) / 25 ≤
      (rowDistribution r Delta (by omega)).toMeasure.real
        {row | rowPairSyndrome row y z ≠ 0} := by sorry
