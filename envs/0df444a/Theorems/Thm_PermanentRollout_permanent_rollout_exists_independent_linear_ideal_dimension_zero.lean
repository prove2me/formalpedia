-- Prove2me | Theorems.Thm_PermanentRollout_permanent_rollout_exists_independent_linear_ideal_dimension_zero
-- name    : PermanentRollout.permanent_rollout_exists_independent_linear_ideal_dimension_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:34.673665+00:00
-- url     : https://prove2.me/theorems/7115004d-77c1-484c-b733-2b9c0acd6180
-- title:
--   PermanentRollout.permanent_rollout_exists_independent_linear_ideal_dimension_zero
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

theorem PermanentRollout.permanent_rollout_exists_independent_linear_ideal_dimension_zero
    {m : ℕ} (I : Ideal (MvPolynomial (Fin m) ℂ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin m) ℂ))
    (r : ℕ)
    (hdim : ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ I) ≤
      (r : WithBot ℕ∞)) :
    ∃ (q : ℕ) (c : Fin q → Fin m → ℂ),
      q ≤ r ∧ LinearIndependent ℂ c ∧
      ringKrullDim
        (MvPolynomial (Fin m) ℂ ⧸
          permanentRolloutHomogeneousLinearSliceIdeal I c) ≤
        (0 : WithBot ℕ∞) := by sorry
