-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_cohomologyDistanceAtLeast_weightReduced_randomFiberBundleData
-- name    : QEC.Coding.FiberBundle.RandomBase.cohomologyDistanceAtLeast_weightReduced_randomFiberBundleData
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:38:22.450439+00:00
-- url     : https://prove2.me/theorems/de5d51f0-95d4-477f-a6a9-61b42eff0a28
-- title:
--   Random Base: cohomology Distance At Least weight Reduced random Fiber Bundle Data
-- statement:
--   The same fully-good HHO20 sample instantiates the cohomological
--   weight-reduction bound with no caller-supplied locality premise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L670-L699
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L670-L699

import Definitions.Def_QEC_Coding_FiberBundle_WeightReduction
import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_HomologyDimension
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open scoped BigOperators
universe u
variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)
local notation "R" => baseSupportRelation D
open QEC.Coding.FiberBundle.RandomBase

theorem QEC.Coding.FiberBundle.RandomBase.cohomologyDistanceAtLeast_weightReduced_randomFiberBundleData
    {r typeCount ell Delta d : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hDelta : 1 ≤ Delta)
    (hGood : IsFullyGood (Delta := Delta) baseSample)
    (hDistance : CohomologyDistanceAtLeast
      (RandomTwist.fiberBundleData baseSample twistSample) d) :
    CohomologyDistanceAtLeast
      (weightReducedData
        (RandomTwist.fiberBundleData baseSample twistSample))
      (d / (101 * Delta)) := by sorry
