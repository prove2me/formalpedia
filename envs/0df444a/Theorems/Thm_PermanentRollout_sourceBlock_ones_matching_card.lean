-- Prove2me | Theorems.Thm_PermanentRollout_sourceBlock_ones_matching_card
-- name    : PermanentRollout.sourceBlock_ones_matching_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:38.420988+00:00
-- url     : https://prove2.me/theorems/0bf60c09-3798-4122-8af8-6e2d23ee7a81
-- title:
--   PermanentRollout.sourceBlock_ones_matching_card
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

theorem PermanentRollout.sourceBlock_ones_matching_card
    (s d : ℕ) (J : Finset (Fin s)) (hJ : J.card = d) :
    Fintype.card
      (Fin (s - d) ≃ {column : Fin s // column ∉ J}) =
      (s - d).factorial := by sorry
