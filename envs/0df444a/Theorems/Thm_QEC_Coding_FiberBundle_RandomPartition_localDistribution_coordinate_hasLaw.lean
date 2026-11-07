-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_localDistribution_coordinate_hasLaw
-- name    : QEC.Coding.FiberBundle.RandomPartition.localDistribution_coordinate_hasLaw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:18:51.903106+00:00
-- url     : https://prove2.me/theorems/4fc74ee7-5300-4d13-81e1-ce8d2b223be8
-- title:
--   Random Partition: local Distribution coordinate has Law
-- statement:
--   Each local bit has its declared Bernoulli law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L170-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L170-L179

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

theorem QEC.Coding.FiberBundle.RandomPartition.localDistribution_coordinate_hasLaw
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (side : Bool) :
    ProbabilityTheory.HasLaw
      (fun localSample : LocalSample => localSample side)
      (localCoordinatePMF r Delta hDelta side).toMeasure
      (localDistribution r Delta hDelta).toMeasure := by sorry
