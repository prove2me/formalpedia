-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_mgf_sum_sampleRowViolationIndicator
-- name    : QEC.Coding.FiberBundle.RandomPartition.mgf_sum_sampleRowViolationIndicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:23:03.667902+00:00
-- url     : https://prove2.me/theorems/a6a523ef-e511-4cce-9771-a2e89cbcd5f6
-- title:
--   Random Partition: mgf sum sample Row Violation Indicator
-- statement:
--   Exact MGF of the violation count on any fixed row set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1177-L1202
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1177-L1202

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

theorem QEC.Coding.FiberBundle.RandomPartition.mgf_sum_sampleRowViolationIndicator
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (y z : Word (ZMod 2) (Fin (4 * r)))
    (rows : Finset (Fin (3 * r))) (t : Real) :
    ProbabilityTheory.mgf
        (fun sample =>
          ∑ a ∈ rows, sampleRowViolationIndicator y z a sample)
        (distribution r Delta hDelta).toMeasure t =
      (1 -
        (rowDistribution r Delta hDelta).toMeasure.real
          {row | rowPairSyndrome row y z ≠ 0} +
        (rowDistribution r Delta hDelta).toMeasure.real
          {row | rowPairSyndrome row y z ≠ 0} * Real.exp t) ^
        rows.card := by sorry
