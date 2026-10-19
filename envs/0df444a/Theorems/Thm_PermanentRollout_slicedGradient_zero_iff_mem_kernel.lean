-- Prove2me | Theorems.Thm_PermanentRollout_slicedGradient_zero_iff_mem_kernel
-- name    : PermanentRollout.slicedGradient_zero_iff_mem_kernel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/ff1f7e73-fa43-43c5-bc41-503457edf5e6
-- title:
--   PermanentRollout.slicedGradient_zero_iff_mem_kernel
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

theorem PermanentRollout.slicedGradient_zero_iff_mem_kernel {m k : ℕ}
    (P : MvPolynomial (Fin m) ℂ)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (u : Fin k → ℂ) :
    (∀ i, MvPolynomial.eval u (slicedGradientPolynomial P W A i) = 0) ↔
      gradientVector P (W u) ∈ LinearMap.ker A := by sorry
