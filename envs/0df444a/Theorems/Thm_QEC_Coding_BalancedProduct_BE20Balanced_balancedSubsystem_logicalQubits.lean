-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_balancedSubsystem_logicalQubits
-- name    : QEC.Coding.BalancedProduct.BE20Balanced.balancedSubsystem_logicalQubits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:53:46.071964+00:00
-- url     : https://prove2.me/theorems/8dd0c58b-f6e2-4184-95d3-e3ae03f485e9
-- title:
--   BE20 Balanced: balanced Subsystem logical Qubits
-- statement:
--   The BE20 Balanced construction uses the balanced Subsystem logical Qubits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamily.lean#L174-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamily.lean#L174-L189

import Definitions.Def_QEC_Coding_BalancedProduct_UnbalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemKernel
import Definitions.Def_QEC_Coding_CSS_SubsystemDual
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Balanced.balancedSubsystem_logicalQubits
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1) :
    (balancedSubsystem q hq40 hq).logicalQubits =
      (sourceSubsystem q hq40 hq).logicalQubits *
        Module.finrank (ZMod 2)
          (LinearMap.ker (balancingBoundary q hq40 hq)) := by sorry
