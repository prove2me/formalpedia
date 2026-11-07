-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_distribution_incidence_iIndepFun
-- name    : QEC.Coding.FiberBundle.RandomPartition.distribution_incidence_iIndepFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:21:10.099204+00:00
-- url     : https://prove2.me/theorems/248468b6-6dbf-49ca-be45-e2b241f8240b
-- title:
--   Random Partition: distribution incidence i Indep Fun
-- statement:
--   All decoded Tanner incidences are mutually independent under the grouped
--   partition sampler.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L259-L275
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L259-L275

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

theorem QEC.Coding.FiberBundle.RandomPartition.distribution_incidence_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun edge : Fin (3 * r) × Fin (4 * r) =>
        fun sample : Sample r => sample edge.1 edge.2 false)
      (distribution r Delta hDelta).toMeasure := by sorry
