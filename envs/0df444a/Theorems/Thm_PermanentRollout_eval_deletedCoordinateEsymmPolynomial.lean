-- Prove2me | Theorems.Thm_PermanentRollout_eval_deletedCoordinateEsymmPolynomial
-- name    : PermanentRollout.eval_deletedCoordinateEsymmPolynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:34.673665+00:00
-- url     : https://prove2.me/theorems/5b3e8604-1050-47d3-b583-f34c08a90cea
-- title:
--   PermanentRollout.eval_deletedCoordinateEsymmPolynomial
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators

theorem PermanentRollout.eval_deletedCoordinateEsymmPolynomial {t : ℕ}
    (u : Fin t → ℂ) (i : Fin t) (q : ℕ) :
    MvPolynomial.eval u (deletedCoordinateEsymmPolynomial t q i) =
      deletedCoordinateEsymm u i q := by sorry
