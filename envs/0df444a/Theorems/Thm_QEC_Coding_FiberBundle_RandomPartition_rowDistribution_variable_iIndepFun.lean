-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowDistribution_variable_iIndepFun
-- name    : QEC.Coding.FiberBundle.RandomPartition.rowDistribution_variable_iIndepFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:18:59.981209+00:00
-- url     : https://prove2.me/theorems/1847bbc1-bf05-49b6-b81a-0366d9695339
-- title:
--   Random Partition: row Distribution variable i Indep Fun
-- statement:
--   Variable-local samples within one check row are mutually independent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L141-L146
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L141-L146

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

theorem QEC.Coding.FiberBundle.RandomPartition.rowDistribution_variable_iIndepFun
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r) :
    ProbabilityTheory.iIndepFun
      (fun b (row : RowSample r) => row b)
      (rowDistribution r Delta hDelta).toMeasure := by sorry
