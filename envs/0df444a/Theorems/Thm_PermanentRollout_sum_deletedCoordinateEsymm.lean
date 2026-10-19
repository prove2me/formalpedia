-- Prove2me | Theorems.Thm_PermanentRollout_sum_deletedCoordinateEsymm
-- name    : PermanentRollout.sum_deletedCoordinateEsymm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:34.673665+00:00
-- url     : https://prove2.me/theorems/4aea34c5-5dc9-4c54-bc42-a3f753d2ac05
-- title:
--   PermanentRollout.sum_deletedCoordinateEsymm
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.sum_deletedCoordinateEsymm {t : ℕ}
    (u : Fin t → ℂ) (q : ℕ) :
    (∑ i : Fin t, deletedCoordinateEsymm u i q) =
      ((t - q : ℕ) : ℂ) * coordinateEsymm u q := by sorry
