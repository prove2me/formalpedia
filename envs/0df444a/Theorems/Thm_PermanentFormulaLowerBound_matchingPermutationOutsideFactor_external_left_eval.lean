-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingPermutationOutsideFactor_external_left_eval
-- name    : PermanentFormulaLowerBound.matchingPermutationOutsideFactor_external_left_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.96597+00:00
-- url     : https://prove2.me/theorems/b738dbcb-453a-42b6-8caa-307296e6b811
-- title:
--   PermanentFormulaLowerBound.matchingPermutationOutsideFactor_external_left_eval
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

theorem PermanentFormulaLowerBound.matchingPermutationOutsideFactor_external_left_eval
    {ell m : ℕ} (p q : Fin m → ℂ)
    (σ : Equiv.Perm (Fin ((ell + ell) + m)))
    (a : Fin m) (u : Fin ell)
    (hσ : σ (matchingBlockIndexEquiv ell m (.inr a)) =
      matchingBlockIndexEquiv ell m (.inl (.inl u))) :
    MvPolynomial.eval (matchingPermanentSpecialization p q)
      (matchingPermutationOutsideFactor (matchingDiagonalEmbedding ell m)
        σ (matchingBlockIndexEquiv ell m (.inr a))) = 1 := by sorry
