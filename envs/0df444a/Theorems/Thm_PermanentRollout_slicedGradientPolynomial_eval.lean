-- Prove2me | Theorems.Thm_PermanentRollout_slicedGradientPolynomial_eval
-- name    : PermanentRollout.slicedGradientPolynomial_eval
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:34.673665+00:00
-- url     : https://prove2.me/theorems/44b0e60f-aa71-488c-b7c4-c6fec2043879
-- title:
--   PermanentRollout.slicedGradientPolynomial_eval
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

theorem PermanentRollout.slicedGradientPolynomial_eval {m k : ℕ}
    (P : MvPolynomial (Fin m) ℂ)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (i : Fin k) (u : Fin k → ℂ) :
    MvPolynomial.eval u (slicedGradientPolynomial P W A i) =
      A (gradientVector P (W u)) i := by sorry
