-- Prove2me | Theorems.Thm_PermanentRollout_exists_injective_inputMap_into_linearCoordinateKernel
-- name    : PermanentRollout.exists_injective_inputMap_into_linearCoordinateKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/f16d7fb7-1d33-4782-bc10-f127f1cc987f
-- title:
--   PermanentRollout.exists_injective_inputMap_into_linearCoordinateKernel
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
attribute [local instance] MvPolynomial.gradedAlgebra

theorem PermanentRollout.exists_injective_inputMap_into_linearCoordinateKernel
    {m k n : ℕ} (c : Fin n → Fin m → ℂ)
    (hk : k + n ≤ m) :
    ∃ W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ),
      Function.Injective W ∧
        ∀ u : Fin k → ℂ, (Matrix.mulVecLin
          (c : Matrix (Fin n) (Fin m) ℂ) :
          (Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (W u) = 0 := by sorry
