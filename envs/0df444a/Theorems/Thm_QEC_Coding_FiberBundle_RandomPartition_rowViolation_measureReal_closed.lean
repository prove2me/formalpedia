-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowViolation_measureReal_closed
-- name    : QEC.Coding.FiberBundle.RandomPartition.rowViolation_measureReal_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:22:00.002791+00:00
-- url     : https://prove2.me/theorems/e6ee79d2-cbf2-4069-beff-ab5527f4533a
-- title:
--   Random Partition: row Violation measure Real closed
-- statement:
--   Exact closed form of HHO20 `prop:chi`: one row violates the paired
--   checks with probability one half minus one half of the XOR/overlap
--   character product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L808-L821
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L808-L821

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

theorem QEC.Coding.FiberBundle.RandomPartition.rowViolation_measureReal_closed
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    (rowDistribution r Delta hDelta).toMeasure.real
        {row | rowPairSyndrome row y z ≠ 0} =
      (1 -
        (1 -
          (RandomBase.incidenceProbability (4 * r) Delta).toReal) ^
            HammingWeight (y + z) *
        (1 -
          2 * (RandomBase.incidenceProbability (4 * r) Delta).toReal) ^
            pairOverlapCount y z) / 2 := by sorry
