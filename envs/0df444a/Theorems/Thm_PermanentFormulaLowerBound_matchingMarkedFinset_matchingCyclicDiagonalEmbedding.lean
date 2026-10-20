-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingMarkedFinset_matchingCyclicDiagonalEmbedding
-- name    : PermanentFormulaLowerBound.matchingMarkedFinset_matchingCyclicDiagonalEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.235103+00:00
-- url     : https://prove2.me/theorems/494cf8eb-d567-42d1-af46-40b28f9fd17f
-- title:
--   PermanentFormulaLowerBound.matchingMarkedFinset_matchingCyclicDiagonalEmbedding
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

theorem PermanentFormulaLowerBound.matchingMarkedFinset_matchingCyclicDiagonalEmbedding
    {n ell : ℕ} (hk : 0 < 2 * ell)
    (t : Fin n) (j : Fin (n / (2 * ell))) :
    matchingMarkedFinset (matchingCyclicDiagonalEmbedding hk t j) =
      cyclicMatchingBlock hk t j := by sorry
