-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_measure_rowViolationSum_le_oneThirdMean_le
-- name    : QEC.Coding.FiberBundle.RandomPartition.measure_rowViolationSum_le_oneThirdMean_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:23:08.18079+00:00
-- url     : https://prove2.me/theorems/9e6881df-8213-4cc5-9931-839a7fd540a5
-- title:
--   Random Partition: measure row Violation Sum le one Third Mean le
-- statement:
--   Multiplicative Chernoff lower tail: fewer than one third of the exact
--   mean has probability at most `exp(-mean/6)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1206-L1308
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1206-L1308

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

theorem QEC.Coding.FiberBundle.RandomPartition.measure_rowViolationSum_le_oneThirdMean_le
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (rows : Finset (Fin (3 * r))) :
    let μ :=
      (rowDistribution r Delta hDelta).toMeasure.real
        {row | rowPairSyndrome row y z ≠ 0}
    (distribution r Delta hDelta).toMeasure.real
        {sample |
          (∑ a ∈ rows,
            sampleRowViolationIndicator y z a sample) ≤
              μ * rows.card / 3} ≤
      Real.exp (-(μ * rows.card) / 6) := by sorry
