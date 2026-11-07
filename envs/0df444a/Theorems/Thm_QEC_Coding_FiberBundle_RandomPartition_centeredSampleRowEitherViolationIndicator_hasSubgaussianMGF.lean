-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_centeredSampleRowEitherViolationIndicator_hasSubgaussianMGF
-- name    : QEC.Coding.FiberBundle.RandomPartition.centeredSampleRowEitherViolationIndicator_hasSubgaussianMGF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:25:29.128886+00:00
-- url     : https://prove2.me/theorems/642d1021-aa73-446a-aa8f-c0b192152e94
-- title:
--   Random Partition: centered Sample Row Either Violation Indicator has Subgaussian MGF
-- statement:
--   Centered heavy-row indicators have Hoeffding parameter `1/4`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2713-L2736
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2713-L2736

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

theorem QEC.Coding.FiberBundle.RandomPartition.centeredSampleRowEitherViolationIndicator_hasSubgaussianMGF
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hDelta : Delta ≤ 4 * r)
    (x : Word (ZMod 2) (Fin (4 * r)))
    (outWord inWord :
      Fin typeCount → Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r)) :
    ProbabilityTheory.HasSubgaussianMGF
      (centeredSampleRowEitherViolationIndicator
        Delta hDelta x outWord inWord a)
      (1 / 4 : NNReal)
      (distribution r Delta hDelta).toMeasure := by sorry
