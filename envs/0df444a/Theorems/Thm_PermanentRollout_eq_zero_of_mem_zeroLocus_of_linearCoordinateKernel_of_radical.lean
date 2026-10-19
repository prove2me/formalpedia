-- Prove2me | Theorems.Thm_PermanentRollout_eq_zero_of_mem_zeroLocus_of_linearCoordinateKernel_of_radical
-- name    : PermanentRollout.eq_zero_of_mem_zeroLocus_of_linearCoordinateKernel_of_radical
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/ee1da417-7fbc-4a13-a8ec-3f4d9c6ea2ec
-- title:
--   PermanentRollout.eq_zero_of_mem_zeroLocus_of_linearCoordinateKernel_of_radical
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

theorem PermanentRollout.eq_zero_of_mem_zeroLocus_of_linearCoordinateKernel_of_radical
    {m n : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ))
    (c : Fin n → Fin m → ℂ)
    (hradical :
      (I ⊔ Ideal.span (Set.range fun j =>
        permanentRolloutLinearCoordinateCombination m (c j))).radical =
        MvPolynomial.idealOfVars (Fin m) ℂ)
    {v : Fin m → ℂ}
    (hv : v ∈ MvPolynomial.zeroLocus ℂ I)
    (hkernel : Matrix.mulVecLin (c : Matrix (Fin n) (Fin m) ℂ) v = 0) :
    v = 0 := by sorry
