-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_balancingBoundary_classicalDistanceAtLeast
-- name    : QEC.Coding.BalancedProduct.BE20Balanced.balancingBoundary_classicalDistanceAtLeast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:53:39.28349+00:00
-- url     : https://prove2.me/theorems/1b77259b-0dfa-4817-9684-df1f0d9c2e20
-- title:
--   BE20 Balanced: balancing Boundary classical Distance At Least
-- statement:
--   The construction-owned quotient Tanner boundary has the classical
--   distance required by EKZ balancing.  The proof extracts the actual attained
--   minimum; no distance parameter is supplied by the caller.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamily.lean#L232-L255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamily.lean#L232-L255

import Definitions.Def_QEC_Coding_BalancedProduct_UnbalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemKernel
import Definitions.Def_QEC_Coding_CSS_SubsystemDual
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Balanced.balancingBoundary_classicalDistanceAtLeast
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1)
    (hLPS : LPS401RayleighBound q hq) :
    ClassicalDistanceAtLeast
      (productData (sourceSubsystem q hq40 hq).dual
        (balancingBoundary q hq40 hq)).classicalBoundary
      (Fintype.card (EdgeOrbit401 q hq) / 10000000) := by sorry
