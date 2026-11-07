-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_exists_fullyGood_hho20_base_and_twist
-- name    : QEC.Coding.FiberBundle.RandomPartition.exists_fullyGood_hho20_base_and_twist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:39:37.571488+00:00
-- url     : https://prove2.me/theorems/ad5ab578-3e05-4c0a-acf2-72963b105e6c
-- title:
--   Random Partition: exists fully Good hho20 base and twist
-- statement:
--   Complete finite random-selection closure before asymptotic parameter
--   specialization: one construction-owned base/twist pair has all random-base
--   properties, partitioned checks, Cayley spectrum, and local testability.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L4261-L4335
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L4261-L4335

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

theorem QEC.Coding.FiberBundle.RandomPartition.exists_fullyGood_hho20_base_and_twist
    (r Delta typeCount ell : Nat)
    [NeZero r] [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hDeltaForty : 40 ≤ Delta)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hDelta : 0 < Delta) (hDeltaOne : 1 ≤ Delta)
    (hTypeSmall : (100 : Real) * typeCount ≤ r)
    (hHeavyScale :
      (100 : Real) * typeCount *
          (1 + 2 * Real.log Delta) ≤
        Delta)
    (hEll : 100001 ≤ ell)
    (hTypeCountSpectrum :
      (40000000000 : Real) * Real.log (ell : Real) ≤
        (typeCount : Real))
    (hNumeric :
      (fullyGoodBaseFailureBound r Delta).toReal +
          ((typeCount : Real) *
              ((1 +
                Real.exp
                  (-(Delta : Real) / (200 * typeCount))) ^
                    (8 * r) - 1) +
            Real.exp (-(r : Real) / 10)) <
        1) :
    ∃ (baseSample : RandomBase.Sample r)
        (twistSample : RandomTwist.Sample r typeCount ell),
      RandomBase.IsFullyGood
          (Delta := Delta) baseSample ∧
        TwistGraph.HasHHO20PartitionedChecks
          Delta baseSample twistSample ∧
        TwistGraph.HasHHO20CayleySpectrum twistSample ∧
        TwistGraph.HasHHO20LocalTestability
          Delta baseSample twistSample := by sorry
