-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_lpsQuotientBoundary_column_weight_le
-- name    : QEC.Coding.BalancedProduct.BE20Balanced.lpsQuotientBoundary_column_weight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:29:15.153709+00:00
-- url     : https://prove2.me/theorems/5e0d52c6-0a02-45e5-9b11-ea7b5e5be54d
-- title:
--   BE20 Balanced: lps Quotient Boundary column weight le
-- statement:
--   The BE20 Balanced construction uses the lps Quotient Boundary column weight le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamilyLocality.lean#L84-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamilyLocality.lean#L84-L93

import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamilyLocality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Balanced.lpsQuotientBoundary_column_weight_le
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1)
    (c : EdgeOrbit401 q hq) :
    HammingWeight (balancingBoundary q hq40 hq (Pi.single c 1)) ≤ 400 := by sorry
