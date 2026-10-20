-- Prove2me | Theorems.Thm_PermanentRollout_blockMinorGraphPullback_rename_matrix
-- name    : PermanentRollout.blockMinorGraphPullback_rename_matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:40.650338+00:00
-- url     : https://prove2.me/theorems/8411e3fb-d170-4c8a-8406-a30c1c0e2337
-- title:
--   PermanentRollout.blockMinorGraphPullback_rename_matrix
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

theorem PermanentRollout.blockMinorGraphPullback_rename_matrix
    (b t s : ℕ) (f : MvPolynomial (Fin (b * t) × Fin s) ℂ) :
    blockMinorGraphPullback b t s
        (MvPolynomial.rename
          (blockMinorMatrixCoordinateLift b t s) f) = f := by sorry
