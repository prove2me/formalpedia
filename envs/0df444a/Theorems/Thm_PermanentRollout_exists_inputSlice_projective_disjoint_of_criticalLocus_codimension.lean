-- Prove2me | Theorems.Thm_PermanentRollout_exists_inputSlice_projective_disjoint_of_criticalLocus_codimension
-- name    : PermanentRollout.exists_inputSlice_projective_disjoint_of_criticalLocus_codimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/4db97336-1c68-499f-9eaf-33342eda3946
-- title:
--   PermanentRollout.exists_inputSlice_projective_disjoint_of_criticalLocus_codimension
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

theorem PermanentRollout.exists_inputSlice_projective_disjoint_of_criticalLocus_codimension
    {m k c d : ℕ} (P : MvPolynomial (Fin m) ℂ)
    (hd : 2 ≤ d) (hP : P.IsHomogeneous d)
    (hk : k ≤ c) (hm : k < m)
    (hcodimension : criticalLocusDimension P ≤
      ((m - c : ℕ) : WithBot ℕ∞)) :
    ∃ W : (Fin k → ℂ) →ₗ[ℂ] (Fin m → ℂ),
      Function.Injective W ∧
      Disjoint
        ((LinearMap.range W).projectivization : Set (ℙ ℂ (Fin m → ℂ)))
        (projectiveCriticalLocus P) := by sorry
