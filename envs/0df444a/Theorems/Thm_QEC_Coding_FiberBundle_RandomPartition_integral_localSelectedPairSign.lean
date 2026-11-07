-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_integral_localSelectedPairSign
-- name    : QEC.Coding.FiberBundle.RandomPartition.integral_localSelectedPairSign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:21:44.531204+00:00
-- url     : https://prove2.me/theorems/fe08809c-908b-4dd2-872f-dcb008652c7d
-- title:
--   Random Partition: integral local Selected Pair Sign
-- statement:
--   Exact expectation of the fair head/tail-selected character.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L513-L541
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L513-L541

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

theorem QEC.Coding.FiberBundle.RandomPartition.integral_localSelectedPairSign
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (b : Fin (4 * r)) :
    ∫ localSample, localSelectedPairSign y z b localSample
      ∂(localDistribution r Delta hDelta).toMeasure =
      (RandomBase.paritySign (y b) +
        RandomBase.paritySign (z b)) / 2 := by sorry
