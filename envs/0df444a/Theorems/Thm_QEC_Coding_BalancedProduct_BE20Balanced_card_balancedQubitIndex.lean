-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_card_balancedQubitIndex
-- name    : QEC.Coding.BalancedProduct.BE20Balanced.card_balancedQubitIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:54:23.928938+00:00
-- url     : https://prove2.me/theorems/35b16c81-3f76-4571-a44c-c4ff6143b437
-- title:
--   BE20 Balanced: card balanced Qubit Index
-- statement:
--   The BE20 Balanced construction uses the card balanced Qubit Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamily.lean#L80-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamily.lean#L80-L92

import Definitions.Def_QEC_Coding_BalancedProduct_UnbalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemKernel
import Definitions.Def_QEC_Coding_CSS_SubsystemDual
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Balanced.card_balancedQubitIndex
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1) :
    Fintype.card (BalancedQubitIndex q hq) =
      blocklengthCoefficient * q * (q ^ 2 - 1) ^ 2 := by sorry
