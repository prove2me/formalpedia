-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowEitherViolation_measureReal_gt_seventyThreeHundredths
-- name    : QEC.Coding.FiberBundle.RandomPartition.rowEitherViolation_measureReal_gt_seventyThreeHundredths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:24:56.055641+00:00
-- url     : https://prove2.me/theorems/56b76121-68b1-4bd1-b118-bf31efbdce48
-- title:
--   Random Partition: row Either Violation measure Real gt seventy Three Hundredths
-- statement:
--   HHO20 heavy-row estimate: with one heavy central word and two light
--   neighbor words, at least one paired check is violated with probability
--   strictly greater than `.73`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2430-L2532
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2430-L2532

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

theorem QEC.Coding.FiberBundle.RandomPartition.rowEitherViolation_measureReal_gt_seventyThreeHundredths
    (r Delta : Nat) (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (x outWord inWord : Word (ZMod 2) (Fin (4 * r)))
    (hx : 4 * (4 * r) ≤ Delta * HammingWeight x)
    (hOut : Delta * HammingWeight outWord ≤ 2 * (4 * r))
    (hIn : Delta * HammingWeight inWord ≤ 2 * (4 * r)) :
    (73 : Real) / 100 <
      (rowDistribution r Delta (by omega)).toMeasure.real
        {row |
          rowPairSyndrome row x outWord ≠ 0 ∨
          rowPairSyndrome row inWord x ≠ 0} := by sorry
