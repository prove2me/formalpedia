-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matching_external_internal_not_mem_diagonal
-- name    : PermanentFormulaLowerBound.matching_external_internal_not_mem_diagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.96597+00:00
-- url     : https://prove2.me/theorems/ad6d0a44-b17d-49b2-9784-9857c7f39469
-- title:
--   PermanentFormulaLowerBound.matching_external_internal_not_mem_diagonal
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

theorem PermanentFormulaLowerBound.matching_external_internal_not_mem_diagonal
    {ell m : ℕ} (a : Fin m) (y : Fin ell ⊕ Fin ell) :
    (matchingBlockIndexEquiv ell m (.inr a),
      matchingBlockIndexEquiv ell m (.inl y)) ∉
        Set.range (matchingDiagonalEmbedding ell m) := by sorry
