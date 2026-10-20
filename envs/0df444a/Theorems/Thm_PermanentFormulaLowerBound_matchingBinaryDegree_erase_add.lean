-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingBinaryDegree_erase_add
-- name    : PermanentFormulaLowerBound.matchingBinaryDegree_erase_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:42.612018+00:00
-- url     : https://prove2.me/theorems/80797cf0-793e-4704-9b9a-e6c279f8d257
-- title:
--   PermanentFormulaLowerBound.matchingBinaryDegree_erase_add
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

theorem PermanentFormulaLowerBound.matchingBinaryDegree_erase_add {ell : ℕ}
    (P : Finset (Fin ell)) (u : Fin ell) (hu : u ∈ P) :
    matchingBinaryDegree (P.erase u) + 2 ^ (u : ℕ) = matchingBinaryDegree P := by sorry
