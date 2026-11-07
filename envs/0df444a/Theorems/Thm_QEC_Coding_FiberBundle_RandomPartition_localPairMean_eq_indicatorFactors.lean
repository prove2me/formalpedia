-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_localPairMean_eq_indicatorFactors
-- name    : QEC.Coding.FiberBundle.RandomPartition.localPairMean_eq_indicatorFactors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:22:04.18811+00:00
-- url     : https://prove2.me/theorems/5836bb5b-0990-48af-9b8e-0538ed9f2c40
-- title:
--   Random Partition: local Pair Mean eq indicator Factors
-- statement:
--   Each local character mean has one factor for the XOR support and one for
--   the overlap support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L750-L779
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L750-L779

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

theorem QEC.Coding.FiberBundle.RandomPartition.localPairMean_eq_indicatorFactors
    (r Delta : Nat)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (b : Fin (4 * r)) :
    1 -
        (RandomBase.incidenceProbability (4 * r) Delta).toReal +
        (RandomBase.incidenceProbability (4 * r) Delta).toReal *
          ((RandomBase.paritySign (y b) +
            RandomBase.paritySign (z b)) / 2) =
      (if y b + z b ≠ 0 then
        1 - (RandomBase.incidenceProbability (4 * r) Delta).toReal
      else 1) *
      (if y b ≠ 0 ∧ z b ≠ 0 then
        1 -
          2 *
            (RandomBase.incidenceProbability (4 * r) Delta).toReal
      else 1) := by sorry
