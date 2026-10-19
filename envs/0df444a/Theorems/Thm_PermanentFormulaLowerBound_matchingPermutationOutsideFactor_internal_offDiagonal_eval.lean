-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingPermutationOutsideFactor_internal_offDiagonal_eval
-- name    : PermanentFormulaLowerBound.matchingPermutationOutsideFactor_internal_offDiagonal_eval
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.96597+00:00
-- url     : https://prove2.me/theorems/598f8b23-a4db-4ce2-a811-8eab607eb49c
-- title:
--   PermanentFormulaLowerBound.matchingPermutationOutsideFactor_internal_offDiagonal_eval
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

theorem PermanentFormulaLowerBound.matchingPermutationOutsideFactor_internal_offDiagonal_eval
    {ell m : ℕ} (p q : Fin m → ℂ)
    (σ : Equiv.Perm (Fin ((ell + ell) + m)))
    (y y' : Fin ell ⊕ Fin ell) (hne : y' ≠ y)
    (hσ : σ (matchingBlockIndexEquiv ell m (.inl y)) =
      matchingBlockIndexEquiv ell m (.inl y')) :
    MvPolynomial.eval (matchingPermanentSpecialization p q)
      (matchingPermutationOutsideFactor
        (matchingDiagonalEmbedding ell m) σ
        (matchingBlockIndexEquiv ell m (.inl y))) = 0 := by sorry
