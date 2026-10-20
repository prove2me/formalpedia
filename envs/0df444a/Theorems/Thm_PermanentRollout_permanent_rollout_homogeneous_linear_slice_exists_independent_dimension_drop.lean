-- Prove2me | Theorems.Thm_PermanentRollout_permanent_rollout_homogeneous_linear_slice_exists_independent_dimension_drop
-- name    : PermanentRollout.permanent_rollout_homogeneous_linear_slice_exists_independent_dimension_drop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:34.673665+00:00
-- url     : https://prove2.me/theorems/ced276f8-d2b7-4f09-9183-7008a6a55c62
-- title:
--   PermanentRollout.permanent_rollout_homogeneous_linear_slice_exists_independent_dimension_drop
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open Set Filter Module
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

theorem PermanentRollout.permanent_rollout_homogeneous_linear_slice_exists_independent_dimension_drop
    {m n : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin m) ℂ))
    (c : Fin n → Fin m → ℂ)
    (hindependent : LinearIndependent ℂ c)
    (hpositive : (0 : WithBot ℕ∞) <
      ringKrullDim
        (MvPolynomial (Fin m) ℂ ⧸
          permanentRolloutHomogeneousLinearSliceIdeal I c)) :
    ∃ x : Fin m → ℂ,
      LinearIndependent ℂ (Fin.snoc c x) ∧
        ringKrullDim
          (MvPolynomial (Fin m) ℂ ⧸
            permanentRolloutHomogeneousLinearSliceIdeal I (Fin.snoc c x)) + 1 ≤
          ringKrullDim
            (MvPolynomial (Fin m) ℂ ⧸
              permanentRolloutHomogeneousLinearSliceIdeal I c) := by sorry
