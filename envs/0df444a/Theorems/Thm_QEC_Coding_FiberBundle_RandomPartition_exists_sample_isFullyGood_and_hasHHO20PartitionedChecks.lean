-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_exists_sample_isFullyGood_and_hasHHO20PartitionedChecks
-- name    : QEC.Coding.FiberBundle.RandomPartition.exists_sample_isFullyGood_and_hasHHO20PartitionedChecks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:26:49.1742+00:00
-- url     : https://prove2.me/theorems/63ba0321-bb8e-42df-9b83-743a22fb0565
-- title:
--   Random Partition: exists sample is Fully Good and has HHO20 Partitioned Checks
-- statement:
--   Exact finite numeric selection theorem for the complete random base
--   layer.  Later parameter lemmas discharge `hNumeric`; it is not exposed by the
--   final code-family theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L4169-L4228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L4169-L4228

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

theorem QEC.Coding.FiberBundle.RandomPartition.exists_sample_isFullyGood_and_hasHHO20PartitionedChecks
    (r Delta typeCount ell : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hDelta : 0 < Delta) (hDeltaOne : 1 ≤ Delta)
    (hTypeSmall : (100 : Real) * typeCount ≤ r)
    (hHeavyScale :
      (100 : Real) * typeCount *
          (1 + 2 * Real.log Delta) ≤
        Delta)
    (typeShifts : Fin typeCount → Fin (ell - 1))
    (hNumeric :
      (fullyGoodBaseFailureBound r Delta).toReal +
          ((typeCount : Real) *
              ((1 +
                Real.exp
                  (-(Delta : Real) / (200 * typeCount))) ^
                    (8 * r) - 1) +
            Real.exp (-(r : Real) / 10)) <
        1) :
    ∃ sample : Sample r,
      RandomBase.IsFullyGood
          (Delta := Delta) (baseSample sample) ∧
        TwistGraph.HasHHO20PartitionedChecks Delta
          (baseSample sample) (twistSample sample typeShifts) := by sorry
