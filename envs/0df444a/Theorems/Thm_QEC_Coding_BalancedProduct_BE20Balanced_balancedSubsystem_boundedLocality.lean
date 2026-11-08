-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_balancedSubsystem_boundedLocality
-- name    : QEC.Coding.BalancedProduct.BE20Balanced.balancedSubsystem_boundedLocality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:28:10.554267+00:00
-- url     : https://prove2.me/theorems/c80a639e-36f3-47d5-ad8d-98b6dd8cf9b1
-- title:
--   BE20 Balanced: balanced Subsystem bounded Locality
-- statement:
--   The final distance-balanced family remains qLDPC.  The bound is the
--   construction-level sum `404 + 402 = 806`; it is independent of `q`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamilyLocality.lean#L114-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamilyLocality.lean#L114-L136

import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamilyLocality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Balanced.balancedSubsystem_boundedLocality
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (balancedSubsystem q hq40 hq).complex).localityProfile 806 := by sorry
