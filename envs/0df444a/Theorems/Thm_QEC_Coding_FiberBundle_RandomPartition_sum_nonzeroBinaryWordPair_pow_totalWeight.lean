-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_sum_nonzeroBinaryWordPair_pow_totalWeight
-- name    : QEC.Coding.FiberBundle.RandomPartition.sum_nonzeroBinaryWordPair_pow_totalWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:24:19.423445+00:00
-- url     : https://prove2.me/theorems/fc289666-3c6f-4d6e-a50f-da9b70ab8014
-- title:
--   Random Partition: sum nonzero Binary Word Pair pow total Weight
-- statement:
--   Removing the all-zero word pair removes exactly the constant term from
--   the pair weight enumerator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1761-L1796
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L1761-L1796

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

theorem QEC.Coding.FiberBundle.RandomPartition.sum_nonzeroBinaryWordPair_pow_totalWeight
    (r : Nat) (t : Real) :
    (∑ pair : NonzeroWordPair r,
        t ^
          (HammingWeight pair.1.1 +
            HammingWeight pair.1.2)) =
      (1 + t) ^ (8 * r) - 1 := by sorry
