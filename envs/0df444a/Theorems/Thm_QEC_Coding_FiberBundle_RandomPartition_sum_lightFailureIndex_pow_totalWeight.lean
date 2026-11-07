-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_sum_lightFailureIndex_pow_totalWeight
-- name    : QEC.Coding.FiberBundle.RandomPartition.sum_lightFailureIndex_pow_totalWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:24:20.052472+00:00
-- url     : https://prove2.me/theorems/7b2d3e7d-4567-4afe-ba46-49a26240670d
-- title:
--   Random Partition: sum light Failure Index pow total Weight
-- statement:
--   Summing geometric weights over all type/nonzero-word indices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1899-L1910
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1899-L1910

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

theorem QEC.Coding.FiberBundle.RandomPartition.sum_lightFailureIndex_pow_totalWeight
    (r typeCount : Nat)
    (t : Real) :
    (∑ index : LightFailureIndex r typeCount,
        t ^
          (HammingWeight index.2.1.1 +
            HammingWeight index.2.1.2)) =
      typeCount * ((1 + t) ^ (8 * r) - 1) := by sorry
