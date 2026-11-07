-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowDistribution_incidence_iIndepFun
-- name    : QEC.Coding.FiberBundle.RandomPartition.rowDistribution_incidence_iIndepFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:21:13.452683+00:00
-- url     : https://prove2.me/theorems/0166bd3e-11f6-45cb-8422-18892553c2f1
-- title:
--   Random Partition: row Distribution incidence i Indep Fun
-- statement:
--   Incidence projections within one partitioned row remain mutually
--   independent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L183-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L183-L191

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

theorem QEC.Coding.FiberBundle.RandomPartition.rowDistribution_incidence_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun b (row : RowSample r) => row b false)
      (rowDistribution r Delta hDelta).toMeasure := by sorry
