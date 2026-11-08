-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_balanced_distance_power_bounds
-- name    : QEC.Coding.BalancedProduct.BE20Balanced.balanced_distance_power_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:54:57.693933+00:00
-- url     : https://prove2.me/theorems/655380f2-d803-4bee-8971-92aa958c7db0
-- title:
--   BE20 Balanced: balanced distance power bounds
-- statement:
--   The BE20 Balanced construction uses the balanced distance power bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamily.lean#L356-L382
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamily.lean#L356-L382

import Definitions.Def_QEC_Coding_BalancedProduct_UnbalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemKernel
import Definitions.Def_QEC_Coding_CSS_SubsystemDual
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Balanced.balanced_distance_power_bounds
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hqLarge : BE20Unbalanced.familyThreshold ≤ q)
    (hq : legendreSym q 401 = -1)
    (hEdgeOrbitLarge : 10000000 ≤ Fintype.card (EdgeOrbit401 q hq)) :
    let N := Fintype.card (BalancedQubitIndex q hq)
    N ^ 3 ≤ dressedXPowerCoefficient *
        (lpsDressedZLowerBound q hq) ^ 5 ∧
      N ^ 3 ≤ dressedZPowerCoefficient *
        ((Fintype.card (EdgeOrbit401 q hq) / 10000000) *
          lpsDressedXLowerBound q) ^ 5 := by sorry
