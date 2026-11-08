-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_q_scale_le_dressedZLowerBound
-- name    : QEC.Coding.BalancedProduct.BE20Balanced.q_scale_le_dressedZLowerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:53:57.675755+00:00
-- url     : https://prove2.me/theorems/a06f3979-7ddc-4639-b0bd-831f6e5fe11a
-- title:
--   BE20 Balanced: q scale le dressed ZLower Bound
-- statement:
--   The BE20 Balanced construction uses the q scale le dressed ZLower Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamily.lean#L305-L354
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamily.lean#L305-L354

import Definitions.Def_QEC_Coding_BalancedProduct_UnbalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemKernel
import Definitions.Def_QEC_Coding_CSS_SubsystemDual
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Balanced.q_scale_le_dressedZLowerBound
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hqLarge : BE20Unbalanced.familyThreshold ≤ q)
    (hq : legendreSym q 401 = -1)
    (hEdgeOrbitLarge : 10000000 ≤ Fintype.card (EdgeOrbit401 q hq)) :
    q * (q ^ 2 - 1) ≤ dressedZLinearCoefficient *
      ((Fintype.card (EdgeOrbit401 q hq) / 10000000) *
        lpsDressedXLowerBound q) := by sorry
