-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_dimension_power_bounds
-- name    : QEC.Coding.BalancedProduct.BE20Balanced.dimension_power_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:54:26.77819+00:00
-- url     : https://prove2.me/theorems/164a0920-fa68-4a45-93b5-a03c1d56ce65
-- title:
--   BE20 Balanced: dimension power bounds
-- statement:
--   The BE20 Balanced construction uses the dimension power bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamily.lean#L120-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamily.lean#L120-L172

import Definitions.Def_QEC_Coding_BalancedProduct_UnbalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_SubsystemKernel
import Definitions.Def_QEC_Coding_CSS_SubsystemDual
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
import Theorems.Thm_QEC_Coding_BalancedProduct_BE20Unbalanced_dimension_power_bounds

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Balanced.dimension_power_bounds
    (q N K : Nat) (hq40 : 40 < q)
    (hN : N = blocklengthCoefficient * q * (q ^ 2 - 1) ^ 2)
    (hKLower : (q ^ 2 - 1) ^ 2 ≤ K)
    (hKUpper : K ≤ (201 * (q ^ 2 - 1)) ^ 2) :
    N ^ 4 ≤ dimensionLowerCoefficient * K ^ 5 ∧
      K ^ 5 ≤ dimensionUpperCoefficient * N ^ 4 := by sorry
