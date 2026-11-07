-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowViolation_measureReal_ge_exp
-- name    : QEC.Coding.FiberBundle.RandomPartition.rowViolation_measureReal_ge_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:22:25.121203+00:00
-- url     : https://prove2.me/theorems/7e65f427-ba0e-47e9-a5c9-e10e8730b792
-- title:
--   Random Partition: row Violation measure Real ge exp
-- statement:
--   HHO20 `prop:chi` exponential lower bound for one partition row.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L951-L986
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L951-L986

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

theorem QEC.Coding.FiberBundle.RandomPartition.rowViolation_measureReal_ge_exp
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (hpHalf :
      (RandomBase.incidenceProbability (4 * r) Delta).toReal ≤
        1 / 2) :
    (1 -
      Real.exp
        (-(RandomBase.incidenceProbability (4 * r) Delta).toReal *
          ((HammingWeight y : Real) + HammingWeight z))) / 2 ≤
      (rowDistribution r Delta hDelta).toMeasure.real
        {row | rowPairSyndrome row y z ≠ 0} := by sorry
