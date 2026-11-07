-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_centeredSampleRowViolationIndicator_hasSubgaussianMGF
-- name    : QEC.Coding.FiberBundle.RandomPartition.centeredSampleRowViolationIndicator_hasSubgaussianMGF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:23:22.052514+00:00
-- url     : https://prove2.me/theorems/53e42e97-69d6-4c68-ab5c-77cdeab27cd3
-- title:
--   Random Partition: centered Sample Row Violation Indicator has Subgaussian MGF
-- statement:
--   Centered row indicators are sub-Gaussian with the sharp Hoeffding
--   parameter `1/4` for variables in `[0,1]`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1323-L1343
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1323-L1343

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

theorem QEC.Coding.FiberBundle.RandomPartition.centeredSampleRowViolationIndicator_hasSubgaussianMGF
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (a : Fin (3 * r)) :
    ProbabilityTheory.HasSubgaussianMGF
      (centeredSampleRowViolationIndicator Delta hDelta y z a)
      (1 / 4 : NNReal)
      (distribution r Delta hDelta).toMeasure := by sorry
