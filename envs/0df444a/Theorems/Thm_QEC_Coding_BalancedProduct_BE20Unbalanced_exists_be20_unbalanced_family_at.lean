-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_BE20Unbalanced_exists_be20_unbalanced_family_at
-- name    : QEC.Coding.BalancedProduct.BE20Unbalanced.exists_be20_unbalanced_family_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T07:43:34.466793+00:00
-- url     : https://prove2.me/theorems/afc4c2c1-e87f-4d27-82bf-a25d95c17900
-- title:
--   BE20 Unbalanced: exists be20 unbalanced family at
-- statement:
--   Construction-indexed unbounded unbalanced family.  The public spectral
--   input is uniform over all admissible primes, while the prime and every code
--   witness are selected internally.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/UnbalancedFamily.lean#L348-L359
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/UnbalancedFamily.lean#L348-L359

import Definitions.Def_QEC_Coding_BalancedProduct_LPSFamily
import Definitions.Def_QEC_Coding_BalancedProduct_UnbalancedFamily
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.BE20Unbalanced
open QEC.Coding
open LPSFamily LPSGraph LPSQuotientTanner

theorem QEC.Coding.BalancedProduct.BE20Unbalanced.exists_be20_unbalanced_family_at
    (hLPS : LPS401FamilyRayleighBound) (B : Nat) :
    ∃ a : AdmissiblePrime401,
      max B familyThreshold < a.q ∧
      UnbalancedFamilyCertificate a.q a.gt40 a.legendre := by sorry
