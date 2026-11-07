-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_integral_paritySign_rowPairSyndrome
-- name    : QEC.Coding.FiberBundle.RandomPartition.integral_paritySign_rowPairSyndrome
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:19:04.175254+00:00
-- url     : https://prove2.me/theorems/6acedcad-fd0a-46c9-917b-60b03046e6c3
-- title:
--   Random Partition: integral parity Sign row Pair Syndrome
-- statement:
--   Exact whole-row parity-character expectation, factored over variables.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L639-L685
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L639-L685

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

theorem QEC.Coding.FiberBundle.RandomPartition.integral_paritySign_rowPairSyndrome
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    ∫ row, RandomBase.paritySign (rowPairSyndrome row y z)
      ∂(rowDistribution r Delta hDelta).toMeasure =
      ∏ b : Fin (4 * r),
        (1 -
          (RandomBase.incidenceProbability (4 * r) Delta).toReal +
          (RandomBase.incidenceProbability (4 * r) Delta).toReal *
            ((RandomBase.paritySign (y b) +
              RandomBase.paritySign (z b)) / 2)) := by sorry
