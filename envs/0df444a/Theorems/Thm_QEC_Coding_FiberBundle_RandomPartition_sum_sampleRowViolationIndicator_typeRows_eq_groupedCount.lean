-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_sum_sampleRowViolationIndicator_typeRows_eq_groupedCount
-- name    : QEC.Coding.FiberBundle.RandomPartition.sum_sampleRowViolationIndicator_typeRows_eq_groupedCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:19:56.511579+00:00
-- url     : https://prove2.me/theorems/386c075e-ea0d-41e5-9c11-b0e582191748
-- title:
--   Random Partition: sum sample Row Violation Indicator type Rows eq grouped Count
-- statement:
--   The real sum of row indicators is the cast of the grouped natural
--   violation count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1427-L1441
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1427-L1441

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

theorem QEC.Coding.FiberBundle.RandomPartition.sum_sampleRowViolationIndicator_typeRows_eq_groupedCount
    {r typeCount : Nat} [NeZero typeCount]
    (sample : Sample r)
    (τ : Fin typeCount)
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    (∑ a ∈ typeRows r typeCount τ,
        sampleRowViolationIndicator y z a sample) =
      (groupedTypeViolationCount sample τ y z : Real) := by sorry
