-- Prove2me | Theorems.Thm_PermanentRollout_linearCoordinatePolynomial_eval
-- name    : PermanentRollout.linearCoordinatePolynomial_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:34.673665+00:00
-- url     : https://prove2.me/theorems/53129629-024a-4c6a-84dd-0ae592ffb1a7
-- title:
--   PermanentRollout.linearCoordinatePolynomial_eval
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization

theorem PermanentRollout.linearCoordinatePolynomial_eval {k m : ℕ}
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (row : Fin m) (u : Fin k → ℂ) :
    MvPolynomial.eval u (linearCoordinatePolynomial W row) = W u row := by sorry
