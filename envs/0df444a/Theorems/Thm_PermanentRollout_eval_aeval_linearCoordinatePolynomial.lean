-- Prove2me | Theorems.Thm_PermanentRollout_eval_aeval_linearCoordinatePolynomial
-- name    : PermanentRollout.eval_aeval_linearCoordinatePolynomial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:34.673665+00:00
-- url     : https://prove2.me/theorems/0dfee178-f75b-4f47-9259-c42eef84a4d4
-- title:
--   PermanentRollout.eval_aeval_linearCoordinatePolynomial
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

theorem PermanentRollout.eval_aeval_linearCoordinatePolynomial {k m : ℕ}
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (u : Fin k → ℂ) (f : MvPolynomial (Fin m) ℂ) :
    MvPolynomial.eval u
        (MvPolynomial.aeval (fun row => linearCoordinatePolynomial W row) f) =
      MvPolynomial.eval (W u) f := by sorry
