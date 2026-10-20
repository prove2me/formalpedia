-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matching_internal_external_not_mem_diagonal
-- name    : PermanentFormulaLowerBound.matching_internal_external_not_mem_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.96597+00:00
-- url     : https://prove2.me/theorems/db978138-2ebb-41ed-8044-d759cd6a00ca
-- title:
--   PermanentFormulaLowerBound.matching_internal_external_not_mem_diagonal
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

theorem PermanentFormulaLowerBound.matching_internal_external_not_mem_diagonal
    {ell m : ℕ} (y : Fin ell ⊕ Fin ell) (b : Fin m) :
    (matchingBlockIndexEquiv ell m (.inl y),
      matchingBlockIndexEquiv ell m (.inr b)) ∉
        Set.range (matchingDiagonalEmbedding ell m) := by sorry
