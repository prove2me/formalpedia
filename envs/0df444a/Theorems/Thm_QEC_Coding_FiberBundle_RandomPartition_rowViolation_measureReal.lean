-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowViolation_measureReal
-- name    : QEC.Coding.FiberBundle.RandomPartition.rowViolation_measureReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:22:08.372211+00:00
-- url     : https://prove2.me/theorems/f8f15114-4997-45a4-a209-b2d1edc48166
-- title:
--   Random Partition: row Violation measure Real
-- statement:
--   Exact HHO20 `prop:chi` probability in product form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L706-L740
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L706-L740

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

theorem QEC.Coding.FiberBundle.RandomPartition.rowViolation_measureReal
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    (rowDistribution r Delta hDelta).toMeasure.real
        {row | rowPairSyndrome row y z ≠ 0} =
      (1 -
        ∏ b : Fin (4 * r),
          (1 -
            (RandomBase.incidenceProbability (4 * r) Delta).toReal +
            (RandomBase.incidenceProbability (4 * r) Delta).toReal *
              ((RandomBase.paritySign (y b) +
                RandomBase.paritySign (z b)) / 2))) / 2 := by sorry
