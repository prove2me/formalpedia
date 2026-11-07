-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_rowDistribution_variable_hasLaw
-- name    : QEC.Coding.FiberBundle.RandomPartition.rowDistribution_variable_hasLaw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:19:08.034703+00:00
-- url     : https://prove2.me/theorems/11c3beac-03e0-4a40-9e52-a495512656a7
-- title:
--   Random Partition: row Distribution variable has Law
-- statement:
--   Every variable-local sample has the two-bit product law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L149-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L149-L159

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

theorem QEC.Coding.FiberBundle.RandomPartition.rowDistribution_variable_hasLaw
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (b : Fin (4 * r)) :
    ProbabilityTheory.HasLaw
      (fun row : RowSample r => row b)
      (localDistribution r Delta hDelta).toMeasure
      (rowDistribution r Delta hDelta).toMeasure := by sorry
