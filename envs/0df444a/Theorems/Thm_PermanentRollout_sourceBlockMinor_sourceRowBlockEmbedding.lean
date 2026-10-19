-- Prove2me | Theorems.Thm_PermanentRollout_sourceBlockMinor_sourceRowBlockEmbedding
-- name    : PermanentRollout.sourceBlockMinor_sourceRowBlockEmbedding
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:40.650338+00:00
-- url     : https://prove2.me/theorems/0f9e1230-5a86-4b07-958b-3a8bfcc09c7c
-- title:
--   PermanentRollout.sourceBlockMinor_sourceRowBlockEmbedding
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.sourceBlockMinor_sourceRowBlockEmbedding
    {R : Type*} [CommSemiring R]
    (b t s : ℕ) (h : Fin b)
    (X : Matrix (Fin (b * t)) (Fin s) R)
    (rows : Finset (Fin t)) (columns : Finset (Fin s)) :
    sourceBlockMinor (b * t) s X
        (rows.map (sourceRowBlockEmbedding b t h)) columns =
      sourceBlockMinor t s
        (fun row column => X (sourceRowBlockEmbedding b t h row) column)
        rows columns := by sorry
