-- Prove2me | Theorems.Thm_PermanentRollout_sourceBlockMatrix_matching_eq_zero_of_invalid
-- name    : PermanentRollout.sourceBlockMatrix_matching_eq_zero_of_invalid
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:38.420988+00:00
-- url     : https://prove2.me/theorems/0a0c037c-4b0b-40a3-8e33-9c20c712d5f7
-- title:
--   PermanentRollout.sourceBlockMatrix_matching_eq_zero_of_invalid
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem PermanentRollout.sourceBlockMatrix_matching_eq_zero_of_invalid
    {R : Type*} [CommSemiring R] (r s d : ℕ)
    (X : Matrix (Fin r) (Fin s) R)
    (U : Matrix (Fin r) (Fin (r - d)) R)
    (matching : (Fin r ⊕ Fin (s - d)) ≃
      (Fin s ⊕ Fin (r - d)))
    (hinvalid : ¬ ∀ row : Fin (s - d),
      ∃ column : Fin s, matching (.inr row) = .inl column) :
    (∏ row, sourceBlockMatrix r s d X U row (matching row)) = 0 := by sorry
