-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowEitherViolation_measureReal
-- name    : QEC.Coding.FiberBundle.RandomPartition.rowEitherViolation_measureReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:24:40.226646+00:00
-- url     : https://prove2.me/theorems/e6479e74-a9b7-457c-b715-0edd36db6044
-- title:
--   Random Partition: row Either Violation measure Real
-- statement:
--   Exact probability of at least one violation among the two paired checks
--   in one row.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2288-L2341
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2288-L2341

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

theorem QEC.Coding.FiberBundle.RandomPartition.rowEitherViolation_measureReal
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (x outWord inWord : Word (ZMod 2) (Fin (4 * r))) :
    (rowDistribution r Delta hDelta).toMeasure.real
        {row |
          rowPairSyndrome row x outWord ≠ 0 ∨
          rowPairSyndrome row inWord x ≠ 0} =
      (3 -
        (∫ row,
          RandomBase.paritySign
            (rowPairSyndrome row x outWord) ∂
              (rowDistribution r Delta hDelta).toMeasure) -
        (∫ row,
          RandomBase.paritySign
            (rowPairSyndrome row inWord x) ∂
              (rowDistribution r Delta hDelta).toMeasure) -
        (∫ row,
          RandomBase.paritySign
            (rowPairSyndrome row
              (x + inWord) (outWord + x)) ∂
              (rowDistribution r Delta hDelta).toMeasure)) / 4 := by sorry
