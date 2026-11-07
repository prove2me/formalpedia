-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_localDistribution_coordinate_iIndepFun
-- name    : QEC.Coding.FiberBundle.RandomPartition.localDistribution_coordinate_iIndepFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:20:56.075504+00:00
-- url     : https://prove2.me/theorems/8eb48db8-89f6-4035-9778-affe1c26a211
-- title:
--   Random Partition: local Distribution coordinate i Indep Fun
-- statement:
--   Incidence and head/tail bits at one possible incidence are independent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L162-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L162-L167

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

theorem QEC.Coding.FiberBundle.RandomPartition.localDistribution_coordinate_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun side (localSample : LocalSample) => localSample side)
      (localDistribution r Delta hDelta).toMeasure := by sorry
