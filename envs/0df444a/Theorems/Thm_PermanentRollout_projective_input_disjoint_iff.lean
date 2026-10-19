-- Prove2me | Theorems.Thm_PermanentRollout_projective_input_disjoint_iff
-- name    : PermanentRollout.projective_input_disjoint_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/9713e953-a6da-40de-bcad-1c06ed964d95
-- title:
--   PermanentRollout.projective_input_disjoint_iff
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

theorem PermanentRollout.projective_input_disjoint_iff {m k : ℕ}
    (P : MvPolynomial (Fin m) ℂ)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (hW : Function.Injective W) :
    Disjoint
      ((LinearMap.range W).projectivization : Set (ℙ ℂ (Fin m → ℂ)))
      (projectiveCriticalLocus P) ↔
      ∀ (u : Fin k → ℂ), u ≠ 0 → gradientVector P (W u) ≠ 0 := by sorry
