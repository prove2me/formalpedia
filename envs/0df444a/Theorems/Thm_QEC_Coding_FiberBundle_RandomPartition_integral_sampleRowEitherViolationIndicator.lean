-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_integral_sampleRowEitherViolationIndicator
-- name    : QEC.Coding.FiberBundle.RandomPartition.integral_sampleRowEitherViolationIndicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:25:36.652749+00:00
-- url     : https://prove2.me/theorems/070d60b4-cb39-467b-b895-7b885275ae3a
-- title:
--   Random Partition: integral sample Row Either Violation Indicator
-- statement:
--   Exact expectation of a named heavy-row indicator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2652-L2695
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2652-L2695

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

theorem QEC.Coding.FiberBundle.RandomPartition.integral_sampleRowEitherViolationIndicator
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hDelta : Delta ≤ 4 * r)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r)) :
    (∫ sample,
        sampleRowEitherViolationIndicator
          x outWord inWord a sample ∂
          (distribution r Delta hDelta).toMeasure) =
      (rowDistribution r Delta hDelta).toMeasure.real
        {row |
          rowPairSyndrome row x
              (outWord (RandomTwist.checkType typeCount a)) ≠ 0 ∨
          rowPairSyndrome row
              (inWord (RandomTwist.checkType typeCount a)) x ≠ 0} := by sorry
