-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_integral_paritySign_rowPairSyndrome_le_exp
-- name    : QEC.Coding.FiberBundle.RandomPartition.integral_paritySign_rowPairSyndrome_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:24:56.312508+00:00
-- url     : https://prove2.me/theorems/134cec49-d0ff-4ed7-9223-652794d5190a
-- title:
--   Random Partition: integral parity Sign row Pair Syndrome le exp
-- statement:
--   Exponential upper envelope for one row parity character.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2210-L2233
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2210-L2233

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

theorem QEC.Coding.FiberBundle.RandomPartition.integral_paritySign_rowPairSyndrome_le_exp
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (hpHalf :
      (RandomBase.incidenceProbability (4 * r) Delta).toReal ≤
        1 / 2) :
    (∫ row,
        RandomBase.paritySign (rowPairSyndrome row y z) ∂
          (rowDistribution r Delta hDelta).toMeasure) ≤
      Real.exp
        (-(RandomBase.incidenceProbability (4 * r) Delta).toReal *
          ((HammingWeight y : Real) + HammingWeight z)) := by sorry
