-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_homologyDistanceAtLeast_weightReduced
-- name    : QEC.Coding.FiberBundle.homologyDistanceAtLeast_weightReduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:15:58.714887+00:00
-- url     : https://prove2.me/theorems/0822daa1-001a-431d-bc41-0d5c2704fcce
-- title:
--   Fiber Bundle: homology Distance At Least weight Reduced
-- statement:
--   HHO20 weight reduction transports homological distance with only the
--   explicit maximum-bit-degree loss.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L303-L312
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/WeightReductionDistance.lean#L303-L312

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

theorem QEC.Coding.FiberBundle.homologyDistanceAtLeast_weightReduced
    (h : ClassicalWeightReduction.HasNoIsolatedVertices R)
    {d L : Nat} (hOne : 1 ≤ L)
    (hBitDegree : ∀ b : baseOne,
      Fintype.card (ClassicalWeightReduction.BitNeighbor R b) ≤ L)
    (hDistance : HomologyDistanceAtLeast D d) :
    HomologyDistanceAtLeast (weightReducedData D) (d / L) := by sorry
