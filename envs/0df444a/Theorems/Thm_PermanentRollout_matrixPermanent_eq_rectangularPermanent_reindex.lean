-- Prove2me | Theorems.Thm_PermanentRollout_matrixPermanent_eq_rectangularPermanent_reindex
-- name    : PermanentRollout.matrixPermanent_eq_rectangularPermanent_reindex
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:40.650338+00:00
-- url     : https://prove2.me/theorems/f3d44d4d-b04b-4601-9264-562151bb8055
-- title:
--   PermanentRollout.matrixPermanent_eq_rectangularPermanent_reindex
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section

theorem PermanentRollout.matrixPermanent_eq_rectangularPermanent_reindex
    {n : ℕ} {α β R : Type*}
    [Fintype α] [Fintype β] [CommSemiring R]
    (row : Fin n ≃ α) (column : Fin n ≃ β)
    (A : Matrix α β R) :
    Matrix.permanent (fun i j : Fin n => A (row i) (column j)) =
      rectangularPermanent A := by sorry
