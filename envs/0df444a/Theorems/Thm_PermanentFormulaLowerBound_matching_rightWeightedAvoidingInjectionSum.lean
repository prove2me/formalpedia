-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matching_rightWeightedAvoidingInjectionSum
-- name    : PermanentFormulaLowerBound.matching_rightWeightedAvoidingInjectionSum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:42.612018+00:00
-- url     : https://prove2.me/theorems/83a8f5d5-b240-4b2a-a450-88b2e88d85fd
-- title:
--   PermanentFormulaLowerBound.matching_rightWeightedAvoidingInjectionSum
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

theorem PermanentFormulaLowerBound.matching_rightWeightedAvoidingInjectionSum
    {F : Type*} [CommSemiring F] {ell m : ℕ}
    (q : Fin m → F) (P Q : Finset (Fin ell)) (a : Fin m) :
    (∑ rho : (↥P ⊕ ↥Q ↪ {j : Fin m // j ≠ a}),
      ∏ v : ↥Q,
        q (rho (Sum.inr v)).1 ^ (2 ^ (v.1 : ℕ))) =
      ((m - 1 - Q.card).descFactorial P.card : F) *
        matchingAvoidingInjectionSum q Q a := by sorry
