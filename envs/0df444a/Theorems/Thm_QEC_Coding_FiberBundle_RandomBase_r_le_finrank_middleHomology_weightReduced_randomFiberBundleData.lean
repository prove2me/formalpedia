-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_r_le_finrank_middleHomology_weightReduced_randomFiberBundleData
-- name    : QEC.Coding.FiberBundle.RandomBase.r_le_finrank_middleHomology_weightReduced_randomFiberBundleData
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:38:33.037187+00:00
-- url     : https://prove2.me/theorems/03d716a3-8c51-4def-8155-d5d235fb0b62
-- title:
--   Random Base: r le finrank middle Homology weight Reduced random Fiber Bundle Data
-- statement:
--   Weight reduction retains the initial HHO20 logical-dimension lower
--   bound, rather than merely preserving a caller-provided abstract rank.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L703-L723
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L703-L723

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

theorem QEC.Coding.FiberBundle.RandomBase.r_le_finrank_middleHomology_weightReduced_randomFiberBundleData
    {r typeCount ell Delta : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hDelta : 1 ≤ Delta)
    (hGood : IsFullyGood (Delta := Delta) baseSample) :
    r ≤ Module.finrank (ZMod 2)
      (chainComplex
        (weightReducedData
          (RandomTwist.fiberBundleData baseSample twistSample))
        ).middleHomology := by sorry
