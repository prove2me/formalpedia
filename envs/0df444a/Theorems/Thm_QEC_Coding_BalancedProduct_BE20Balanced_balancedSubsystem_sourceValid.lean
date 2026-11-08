-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_balancedSubsystem_sourceValid
-- name    : QEC.Coding.BalancedProduct.BE20Balanced.balancedSubsystem_sourceValid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:28:40.220579+00:00
-- url     : https://prove2.me/theorems/48c62a40-7214-4f84-99f1-1f8b2e450130
-- title:
--   BE20 Balanced: balanced Subsystem source Valid
-- statement:
--   The BE20 Balanced construction uses the balanced Subsystem source Valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamilyLocality.lean#L138-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamilyLocality.lean#L138-L143

import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamilyLocality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Balanced.balancedSubsystem_sourceValid
    (q : Nat) [Fact q.Prime]
    (hq40 : 40 < q) (hq : legendreSym q 401 = -1) :
    ((balancedSubsystem q hq40 hq).complex.binaryCSSCode).stabilizer.IsSourceValidBinary := by sorry
