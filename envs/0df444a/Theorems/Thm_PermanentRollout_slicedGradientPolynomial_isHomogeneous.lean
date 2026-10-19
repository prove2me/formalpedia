-- Prove2me | Theorems.Thm_PermanentRollout_slicedGradientPolynomial_isHomogeneous
-- name    : PermanentRollout.slicedGradientPolynomial_isHomogeneous
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:34.673665+00:00
-- url     : https://prove2.me/theorems/6127bb4f-713c-48b1-b57f-00da7f91f17f
-- title:
--   PermanentRollout.slicedGradientPolynomial_isHomogeneous
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

theorem PermanentRollout.slicedGradientPolynomial_isHomogeneous {m k d : ℕ}
    (P : MvPolynomial (Fin m) ℂ)
    (hP : P.IsHomogeneous d)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (i : Fin k) :
    (slicedGradientPolynomial P W A i).IsHomogeneous (d - 1) := by sorry
