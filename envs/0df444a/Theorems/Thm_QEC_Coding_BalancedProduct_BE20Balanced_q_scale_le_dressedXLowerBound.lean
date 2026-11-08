-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_q_scale_le_dressedXLowerBound
-- name    : QEC.Coding.BalancedProduct.BE20Balanced.q_scale_le_dressedXLowerBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:53:57.772197+00:00
-- url     : https://prove2.me/theorems/dc8ad474-1cb5-4fa4-a95b-f31fdf3ae1d0
-- title:
--   BE20 Balanced: q scale le dressed XLower Bound
-- statement:
--   The BE20 Balanced construction uses the q scale le dressed XLower Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamily.lean#L289-L303
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamily.lean#L289-L303

import Definitions.Def_QEC_Coding_BalancedProduct_UnbalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemKernel
import Definitions.Def_QEC_Coding_CSS_SubsystemDual
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Balanced.q_scale_le_dressedXLowerBound
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hqLarge : BE20Unbalanced.familyThreshold ≤ q)
    (hq : legendreSym q 401 = -1) :
    q * (q ^ 2 - 1) ≤
      BE20Unbalanced.dressedZCoefficient * lpsDressedZLowerBound q hq := by sorry
