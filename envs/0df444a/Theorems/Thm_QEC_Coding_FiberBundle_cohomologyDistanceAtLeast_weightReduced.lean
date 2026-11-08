-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_cohomologyDistanceAtLeast_weightReduced
-- name    : QEC.Coding.FiberBundle.cohomologyDistanceAtLeast_weightReduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:17:59.732129+00:00
-- url     : https://prove2.me/theorems/d1a81f14-7140-4286-b06b-983a230ff2d0
-- title:
--   Fiber Bundle: cohomology Distance At Least weight Reduced
-- statement:
--   HHO20 weight reduction transports cohomological distance with only the
--   explicit maximum-check-degree loss.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L622-L631
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L622-L631

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

theorem QEC.Coding.FiberBundle.cohomologyDistanceAtLeast_weightReduced
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    {d L : Nat} (hOne : 1 ≤ L)
    (hCheckDegree : ∀ c : baseZero,
      Fintype.card (ClassicalWeightReduction.CheckNeighbor R c) ≤ L)
    (hDistance : CohomologyDistanceAtLeast D d) :
    CohomologyDistanceAtLeast (weightReducedData D) (d / L) := by sorry
