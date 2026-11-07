-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_integral_localIncidenceReal
-- name    : QEC.Coding.FiberBundle.RandomPartition.integral_localIncidenceReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:18:56.630286+00:00
-- url     : https://prove2.me/theorems/51a72aba-ce75-4d8f-952a-204c9ae20580
-- title:
--   Random Partition: integral local Incidence Real
-- statement:
--   Exact expectation of the local incidence indicator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L492-L510
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L492-L510

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

theorem QEC.Coding.FiberBundle.RandomPartition.integral_localIncidenceReal
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ∫ localSample, localIncidenceReal localSample
      ∂(localDistribution r Delta hDelta).toMeasure =
      (RandomBase.incidenceProbability (4 * r) Delta).toReal := by sorry
