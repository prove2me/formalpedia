-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_integral_localIncidenceReal_mul_selectedPairSign
-- name    : QEC.Coding.FiberBundle.RandomPartition.integral_localIncidenceReal_mul_selectedPairSign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:21:58.81685+00:00
-- url     : https://prove2.me/theorems/f530b478-eb7f-40bc-ab41-57ce4350e09b
-- title:
--   Random Partition: integral local Incidence Real mul selected Pair Sign
-- statement:
--   Exact expectation of the product of the independent local factors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L568-L592
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L568-L592

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

theorem QEC.Coding.FiberBundle.RandomPartition.integral_localIncidenceReal_mul_selectedPairSign
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (b : Fin (4 * r)) :
    ∫ localSample,
        localIncidenceReal localSample *
          localSelectedPairSign y z b localSample
      ∂(localDistribution r Delta hDelta).toMeasure =
      (RandomBase.incidenceProbability (4 * r) Delta).toReal *
        ((RandomBase.paritySign (y b) +
          RandomBase.paritySign (z b)) / 2) := by sorry
