-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matching_leftWeightedAvoidingInjectionSum
-- name    : PermanentFormulaLowerBound.matching_leftWeightedAvoidingInjectionSum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:42.612018+00:00
-- url     : https://prove2.me/theorems/45d0701e-17f2-4da6-a8f2-ca9fa436e5e7
-- title:
--   PermanentFormulaLowerBound.matching_leftWeightedAvoidingInjectionSum
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin

theorem PermanentFormulaLowerBound.matching_leftWeightedAvoidingInjectionSum
    {F : Type*} [CommSemiring F] {ell m : ℕ}
    (p : Fin m → F) (P Q : Finset (Fin ell)) (b : Fin m) :
    (∑ rho : (↥P ⊕ ↥Q ↪ {j : Fin m // j ≠ b}),
      ∏ u : ↥P,
        p (rho (Sum.inl u)).1 ^ (2 ^ (u.1 : ℕ))) =
      ((m - 1 - P.card).descFactorial Q.card : F) *
        matchingAvoidingInjectionSum p P b := by sorry
