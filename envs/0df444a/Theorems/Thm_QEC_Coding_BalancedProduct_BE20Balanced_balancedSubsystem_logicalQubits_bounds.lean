-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_balancedSubsystem_logicalQubits_bounds
-- name    : QEC.Coding.BalancedProduct.BE20Balanced.balancedSubsystem_logicalQubits_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:54:26.296998+00:00
-- url     : https://prove2.me/theorems/14a39f78-9aec-49f0-8500-c42606141f89
-- title:
--   BE20 Balanced: balanced Subsystem logical Qubits bounds
-- statement:
--   The BE20 Balanced construction uses the balanced Subsystem logical Qubits bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamily.lean#L191-L227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamily.lean#L191-L227

import Definitions.Def_QEC_Coding_BalancedProduct_UnbalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemKernel
import Definitions.Def_QEC_Coding_CSS_SubsystemDual
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Balanced.balancedSubsystem_logicalQubits_bounds
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1) :
    (q ^ 2 - 1) ^ 2 ≤ (balancedSubsystem q hq40 hq).logicalQubits ∧
      (balancedSubsystem q hq40 hq).logicalQubits ≤
        (201 * (q ^ 2 - 1)) ^ 2 := by sorry
