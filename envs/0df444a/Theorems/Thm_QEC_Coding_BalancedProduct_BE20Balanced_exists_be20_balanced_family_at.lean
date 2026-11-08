-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Balanced_exists_be20_balanced_family_at
-- name    : QEC.Coding.BalancedProduct.BE20Balanced.exists_be20_balanced_family_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:51:09.808914+00:00
-- url     : https://prove2.me/theorems/f40e5673-3d72-44ea-a74e-c98963657dcb
-- title:
--   BE20 Balanced: exists be20 balanced family at
-- statement:
--   Construction-indexed unbounded balanced family.  The LPS premise is
--   uniform and graph-only; the prime, code, quotient Tanner factor, and all
--   finite witnesses are selected internally.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamilyLocality.lean#L215-L226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/BalancedFamilyLocality.lean#L215-L226

import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamily
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Definitions.Def_QEC_Coding_BalancedProduct_BalancedFamilyLocality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Balanced
open QEC.Coding
open DistanceBalancing DistanceBalancingSubsystem
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Balanced.exists_be20_balanced_family_at
    (hLPS : LPS401FamilyRayleighBound) (B : Nat) :
    ∃ a : AdmissiblePrime401,
      max B BE20Unbalanced.familyThreshold < a.q ∧
      BalancedFamilyCertificate a.q a.gt40 a.legendre := by sorry
