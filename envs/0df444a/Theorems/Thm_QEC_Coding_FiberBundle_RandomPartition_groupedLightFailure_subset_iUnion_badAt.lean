-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_groupedLightFailure_subset_iUnion_badAt
-- name    : QEC.Coding.FiberBundle.RandomPartition.groupedLightFailure_subset_iUnion_badAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:23:59.430395+00:00
-- url     : https://prove2.me/theorems/e940ee03-5c20-4f2b-a18f-728beb867926
-- title:
--   Random Partition: grouped Light Failure subset i Union bad At
-- statement:
--   Failure of the simultaneous grouped light event is covered by the
--   finite union of nonzero fixed-triple bad events.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1834-L1854
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1834-L1854

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

theorem QEC.Coding.FiberBundle.RandomPartition.groupedLightFailure_subset_iUnion_badAt
    (r Delta typeCount : Nat) [NeZero typeCount] :
    {sample | ¬ HasGroupedHHO20LightChecks
      (r := r) (typeCount := typeCount) Delta sample} ⊆
      ⋃ index : LightFailureIndex r typeCount,
        groupedLightBadAt r Delta typeCount index := by sorry
