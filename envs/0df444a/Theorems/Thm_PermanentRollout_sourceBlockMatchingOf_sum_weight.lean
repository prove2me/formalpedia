-- Prove2me | Theorems.Thm_PermanentRollout_sourceBlockMatchingOf_sum_weight
-- name    : PermanentRollout.sourceBlockMatchingOf_sum_weight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:38.420988+00:00
-- url     : https://prove2.me/theorems/079cdd49-441d-4828-b153-9c9aef4f615a
-- title:
--   PermanentRollout.sourceBlockMatchingOf_sum_weight
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

theorem PermanentRollout.sourceBlockMatchingOf_sum_weight
    {R : Type*} [CommSemiring R] (r s d : ℕ)
    (X : Matrix (Fin r) (Fin s) R)
    (U : Matrix (Fin r) (Fin (r - d)) R)
    (I : Finset (Fin r)) (J : Finset (Fin s))
    (hJ : J.card = d) :
    (∑ variableMatching : I ≃ J,
      ∑ constantMatching :
        {row : Fin r // row ∉ I} ≃ Fin (r - d),
      ∑ onesMatching :
        Fin (s - d) ≃ {column : Fin s // column ∉ J},
        ∏ row, sourceBlockMatrix r s d X U row
          (sourceBlockMatchingOf r s d I J
            variableMatching constantMatching onesMatching row)) =
      ((s - d).factorial : R) *
        (sourceBlockAlpha r d U I * sourceBlockMinor r s X I J) := by sorry
