-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_distance_power_bound_of_linear_q_scale
-- name    : QEC.Coding.BalancedProduct.BE20Balanced.distance_power_bound_of_linear_q_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:53:35.944232+00:00
-- url     : https://prove2.me/theorems/0ce1a4f2-754c-4bea-97ef-3fca5b20a468
-- title:
--   BE20 Balanced: distance power bound of linear q scale
-- statement:
--   A reusable integral form of the exponent conversion
--   `N = C q(q²-1)²` and `q(q²-1) = O(d)` imply `N³ = O(d⁵)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamily.lean#L96-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamily.lean#L96-L118

import Definitions.Def_QEC_Coding_BalancedProduct_UnbalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemKernel
import Definitions.Def_QEC_Coding_CSS_SubsystemDual
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Balanced.distance_power_bound_of_linear_q_scale
    (q N d coefficient : Nat)
    (hN : N = blocklengthCoefficient * q * (q ^ 2 - 1) ^ 2)
    (hqd : q * (q ^ 2 - 1) ≤ coefficient * d) :
    N ^ 3 ≤ blocklengthCoefficient ^ 3 * coefficient ^ 5 * d ^ 5 := by sorry
