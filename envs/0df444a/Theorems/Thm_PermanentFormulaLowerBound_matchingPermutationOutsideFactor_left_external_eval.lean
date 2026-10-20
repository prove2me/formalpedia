-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingPermutationOutsideFactor_left_external_eval
-- name    : PermanentFormulaLowerBound.matchingPermutationOutsideFactor_left_external_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.96597+00:00
-- url     : https://prove2.me/theorems/9b4b9f7e-4e1f-455b-b17c-2681a02530d8
-- title:
--   PermanentFormulaLowerBound.matchingPermutationOutsideFactor_left_external_eval
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

theorem PermanentFormulaLowerBound.matchingPermutationOutsideFactor_left_external_eval
    {ell m : ℕ} (p q : Fin m → ℂ)
    (σ : Equiv.Perm (Fin ((ell + ell) + m)))
    (u : Fin ell) (b : Fin m)
    (hσ : σ (matchingBlockIndexEquiv ell m (.inl (.inl u))) =
      matchingBlockIndexEquiv ell m (.inr b)) :
    MvPolynomial.eval (matchingPermanentSpecialization p q)
      (matchingPermutationOutsideFactor (matchingDiagonalEmbedding ell m)
        σ (matchingBlockIndexEquiv ell m (.inl (.inl u)))) =
      p b ^ (2 ^ (u : ℕ)) := by sorry
