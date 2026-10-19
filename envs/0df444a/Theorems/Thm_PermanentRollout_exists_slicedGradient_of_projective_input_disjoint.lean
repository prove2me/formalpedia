-- Prove2me | Theorems.Thm_PermanentRollout_exists_slicedGradient_of_projective_input_disjoint
-- name    : PermanentRollout.exists_slicedGradient_of_projective_input_disjoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/baf610b3-df55-4bae-951b-3326cab088cb
-- title:
--   PermanentRollout.exists_slicedGradient_of_projective_input_disjoint
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

theorem PermanentRollout.exists_slicedGradient_of_projective_input_disjoint {m k d : ℕ}
    (P : MvPolynomial (Fin m) ℂ)
    (hd : 2 ≤ d) (hP : P.IsHomogeneous d)
    (W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (hW : Function.Injective W)
    (hinput : Disjoint
      ((LinearMap.range W).projectivization : Set (ℙ ℂ (Fin m → ℂ)))
      (projectiveCriticalLocus P)) :
    ∃ A : (Fin m → ℂ) →ₗ[ℂ] (Fin k → ℂ),
      (∀ i : Fin k,
        (slicedGradientPolynomial P W A i).IsHomogeneous (d - 1)) ∧
      (∀ u : Fin k → ℂ,
        (∀ i : Fin k,
          MvPolynomial.eval u (slicedGradientPolynomial P W A i) = 0) ↔
            u = 0) := by sorry
