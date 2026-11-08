-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_lpsQuotientBoundary_row_weight_le
-- name    : QEC.Coding.BalancedProduct.BE20Balanced.lpsQuotientBoundary_row_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:28:33.028455+00:00
-- url     : https://prove2.me/theorems/fd8b49bc-78bf-4194-ad62-9fa02c7a73dc
-- title:
--   BE20 Balanced: lps Quotient Boundary row weight le
-- statement:
--   The BE20 Balanced construction uses the lps Quotient Boundary row weight le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamilyLocality.lean#L95-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamilyLocality.lean#L95-L110

import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamilyLocality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Balanced.lpsQuotientBoundary_row_weight_le
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1)
    (r : CheckOrbit401 q) :
    HammingWeight
      (wordLinearMapTranspose (balancingBoundary q hq40 hq)
        (Pi.single r 1)) ≤ 402 := by sorry
