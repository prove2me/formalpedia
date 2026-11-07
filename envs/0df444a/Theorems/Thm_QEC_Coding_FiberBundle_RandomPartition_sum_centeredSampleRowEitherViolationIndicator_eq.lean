-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_sum_centeredSampleRowEitherViolationIndicator_eq
-- name    : QEC.Coding.FiberBundle.RandomPartition.sum_centeredSampleRowEitherViolationIndicator_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:20:24.030289+00:00
-- url     : https://prove2.me/theorems/103a371e-95b4-4d8a-bd78-459a9c685bd1
-- title:
--   Random Partition: sum centered Sample Row Either Violation Indicator eq
-- statement:
--   Sum of centered heavy-row indicators equals raw count minus the sum of
--   their exact means.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2868-L2888
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2868-L2888

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

theorem QEC.Coding.FiberBundle.RandomPartition.sum_centeredSampleRowEitherViolationIndicator_eq
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hDelta : Delta ≤ 4 * r)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r)))
    (rows : Finset (Fin (3 * r)))
    (sample : Sample r) :
    (∑ a ∈ rows,
      centeredSampleRowEitherViolationIndicator
        Delta hDelta x outWord inWord a sample) =
      (∑ a ∈ rows,
        sampleRowEitherViolationIndicator
          x outWord inWord a sample) -
      ∑ a ∈ rows,
        ∫ sample',
          sampleRowEitherViolationIndicator
            x outWord inWord a sample' ∂
            (distribution r Delta hDelta).toMeasure := by sorry
