-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_measure_centeredRowEitherViolationSum_le_neg_le
-- name    : QEC.Coding.FiberBundle.RandomPartition.measure_centeredRowEitherViolationSum_le_neg_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:20:00.472872+00:00
-- url     : https://prove2.me/theorems/f877290d-f762-475f-9585-ce836ea1ac5c
-- title:
--   Random Partition: measure centered Row Either Violation Sum le neg le
-- statement:
--   Hoeffding lower tail for any fixed collection of heavy rows.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2762-L2808
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2762-L2808

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

theorem QEC.Coding.FiberBundle.RandomPartition.measure_centeredRowEitherViolationSum_le_neg_le
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hDelta : Delta ≤ 4 * r)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r)))
    (rows : Finset (Fin (3 * r)))
    (ε : Real) (hε : 0 ≤ ε) :
    (distribution r Delta hDelta).toMeasure.real
        {sample |
          (∑ a ∈ rows,
            centeredSampleRowEitherViolationIndicator
              Delta hDelta x outWord inWord a sample) ≤ -ε} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ↑(∑ _a ∈ rows, (1 / 4 : NNReal)))) := by sorry
