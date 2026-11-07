-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_distribution_baseSample_measureReal_eq
-- name    : QEC.Coding.FiberBundle.RandomPartition.distribution_baseSample_measureReal_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:21:23.168094+00:00
-- url     : https://prove2.me/theorems/93c3f269-6659-4587-a11b-38c8aa0b03f2
-- title:
--   Random Partition: distribution base Sample measure Real eq
-- statement:
--   Exact transfer of every event measure through the decoded incidence
--   projection.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L333-L342
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L333-L342

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

theorem QEC.Coding.FiberBundle.RandomPartition.distribution_baseSample_measureReal_eq
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (event : RandomBase.Sample r → Prop) :
    (distribution r Delta hDelta).toMeasure.real
        {sample | event (baseSample sample)} =
      (RandomBase.distribution r Delta hDelta).toMeasure.real
        {base | event base} := by sorry
