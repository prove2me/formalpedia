-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_integral_localPairSign
-- name    : QEC.Coding.FiberBundle.RandomPartition.integral_localPairSign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:21:58.544983+00:00
-- url     : https://prove2.me/theorems/28f88258-be5b-425e-a6cc-76d0ced42c5e
-- title:
--   Random Partition: integral local Pair Sign
-- statement:
--   Exact HHO20 local character expectation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L595-L636
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L595-L636

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

theorem QEC.Coding.FiberBundle.RandomPartition.integral_localPairSign
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (b : Fin (4 * r)) :
    ∫ localSample, localPairSign y z b localSample
      ∂(localDistribution r Delta hDelta).toMeasure =
      1 -
        (RandomBase.incidenceProbability (4 * r) Delta).toReal +
        (RandomBase.incidenceProbability (4 * r) Delta).toReal *
          ((RandomBase.paritySign (y b) +
            RandomBase.paritySign (z b)) / 2) := by sorry
