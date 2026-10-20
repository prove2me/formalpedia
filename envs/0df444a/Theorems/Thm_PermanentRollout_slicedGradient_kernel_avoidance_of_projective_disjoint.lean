-- Prove2me | Theorems.Thm_PermanentRollout_slicedGradient_kernel_avoidance_of_projective_disjoint
-- name    : PermanentRollout.slicedGradient_kernel_avoidance_of_projective_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/5cc29331-4e37-4bd1-bfb5-5dae681aa47f
-- title:
--   PermanentRollout.slicedGradient_kernel_avoidance_of_projective_disjoint
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

theorem PermanentRollout.slicedGradient_kernel_avoidance_of_projective_disjoint
    {m k : ℕ} (P : MvPolynomial (Fin m) ℂ)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ))
    (hnonzero : ∀ (u : Fin k → ℂ), u ≠ 0 →
      gradientVector P (W u) ≠ 0)
    (hdisjoint : Disjoint
      (projectiveSlicedGradientImage P W)
      ((LinearMap.ker A).projectivization : Set (ℙ ℂ (Fin m → ℂ)))) :
    ∀ (u : Fin k → ℂ), u ≠ 0 →
      gradientVector P (W u) ∉ LinearMap.ker A := by sorry
