-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_balancedSubsystem_dressedDistanceBounds
-- name    : QEC.Coding.BalancedProduct.BE20Balanced.balancedSubsystem_dressedDistanceBounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:55:27.445309+00:00
-- url     : https://prove2.me/theorems/9214342b-b72f-4bbb-9c57-b888c8613c52
-- title:
--   BE20 Balanced: balanced Subsystem dressed Distance Bounds
-- statement:
--   Both balanced dressed distances follow from the already-certified
--   unbalanced distances.  Dualization is essential: the classical distance
--   multiplies the formerly short dressed-X side.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamily.lean#L260-L287
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamily.lean#L260-L287

import Definitions.Def_QEC_Coding_BalancedProduct_UnbalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemKernel
import Definitions.Def_QEC_Coding_CSS_SubsystemDual
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Balanced.balancedSubsystem_dressedDistanceBounds
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq804 : 804 ≤ q)
    (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq)
    (hEdgeOrbitLarge : 10000000 ≤ Fintype.card (EdgeOrbit401 q hq))
    (hCheckOrbitLarge : 10000000 ≤ Fintype.card (CheckOrbit401 q)) :
    (balancedSubsystem q hq40 hq).DressedXDistanceAtLeast
        (lpsDressedZLowerBound q hq) ∧
      (balancedSubsystem q hq40 hq).DressedZDistanceAtLeast
        ((Fintype.card (EdgeOrbit401 q hq) / 10000000) *
          lpsDressedXLowerBound q) := by sorry
