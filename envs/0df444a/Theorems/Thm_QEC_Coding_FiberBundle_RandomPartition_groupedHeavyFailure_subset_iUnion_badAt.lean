-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_groupedHeavyFailure_subset_iUnion_badAt
-- name    : QEC.Coding.FiberBundle.RandomPartition.groupedHeavyFailure_subset_iUnion_badAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:25:48.656013+00:00
-- url     : https://prove2.me/theorems/c5630a2c-aea3-4de3-baf5-cd2cfd501521
-- title:
--   Random Partition: grouped Heavy Failure subset i Union bad At
-- statement:
--   Failure of the full deterministic heavy-check interface is covered by
--   the finite union of normalized globally-light configurations.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3356-L3426
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3356-L3426

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

theorem QEC.Coding.FiberBundle.RandomPartition.groupedHeavyFailure_subset_iUnion_badAt
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (typeShifts : Fin typeCount → Fin (ell - 1)) :
    {sample |
      ¬TwistGraph.HasHHO20HeavyChecks Delta
        (baseSample sample) (twistSample sample typeShifts)} ⊆
      ⋃ index : HeavyFailureIndex r Delta typeCount,
        groupedHeavyBadAt
          r Delta typeCount ell typeShifts index := by sorry
