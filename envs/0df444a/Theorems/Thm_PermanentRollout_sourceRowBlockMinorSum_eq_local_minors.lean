-- Prove2me | Theorems.Thm_PermanentRollout_sourceRowBlockMinorSum_eq_local_minors
-- name    : PermanentRollout.sourceRowBlockMinorSum_eq_local_minors
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:40.650338+00:00
-- url     : https://prove2.me/theorems/c0fe700a-347d-4154-9043-3c593c77827d
-- title:
--   PermanentRollout.sourceRowBlockMinorSum_eq_local_minors
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.sourceRowBlockMinorSum_eq_local_minors
    {R : Type*} [CommSemiring R]
    (b t s d : ℕ) (h : Fin b)
    (X : Matrix (Fin (b * t)) (Fin s) R) :
    sourceRowBlockMinorSum b t s d X h =
      ∑ rows ∈ (Finset.univ : Finset (Fin t)).powersetCard d,
        ∑ columns ∈ (Finset.univ : Finset (Fin s)).powersetCard d,
          sourceBlockMinor t s
            (fun row column => X (sourceRowBlockEmbedding b t h row) column)
            rows columns := by sorry
