-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_measure_centeredRowViolationSum_le_neg_le
-- name    : QEC.Coding.FiberBundle.RandomPartition.measure_centeredRowViolationSum_le_neg_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:32:07.052385+00:00
-- url     : https://prove2.me/theorems/de91ad37-0e1e-43b1-be46-bcef6ce229cc
-- title:
--   Random Partition: measure centered Row Violation Sum le neg le
-- statement:
--   Hoeffding lower tail for the violation count on any fixed set of rows.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1364-L1407
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1364-L1407

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

theorem QEC.Coding.FiberBundle.RandomPartition.measure_centeredRowViolationSum_le_neg_le
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (rows : Finset (Fin (3 * r)))
    (ε : Real) (hε : 0 ≤ ε) :
    (distribution r Delta hDelta).toMeasure.real
        {sample |
          (∑ a ∈ rows,
            centeredSampleRowViolationIndicator
              Delta hDelta y z a sample) ≤ -ε} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ↑(∑ _a ∈ rows, (1 / 4 : NNReal)))) := by sorry
