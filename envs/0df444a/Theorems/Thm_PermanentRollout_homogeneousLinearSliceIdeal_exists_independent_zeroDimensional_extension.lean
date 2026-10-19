-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousLinearSliceIdeal_exists_independent_zeroDimensional_extension
-- name    : PermanentRollout.homogeneousLinearSliceIdeal_exists_independent_zeroDimensional_extension
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:34.673665+00:00
-- url     : https://prove2.me/theorems/c849a67c-8bb8-4dda-b1f9-66c6a81e5120
-- title:
--   PermanentRollout.homogeneousLinearSliceIdeal_exists_independent_zeroDimensional_extension
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra

theorem PermanentRollout.homogeneousLinearSliceIdeal_exists_independent_zeroDimensional_extension
    {t p : ℕ} (I : Ideal (MvPolynomial (Fin t) ℂ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin t) ℂ))
    (c : Fin p → Fin t → ℂ)
    (hindependent : LinearIndependent ℂ c)
    (q : ℕ) (hlength : p + q ≤ t)
    (hdimension : ringKrullDim
      (MvPolynomial (Fin t) ℂ ⧸ homogeneousLinearSliceIdeal I c) ≤
        (↑q : WithBot ℕ∞)) :
    ∃ x : Fin (p + q) → Fin t → ℂ,
      LinearIndependent ℂ x ∧
        ringKrullDim
          (MvPolynomial (Fin t) ℂ ⧸ homogeneousLinearSliceIdeal I x) ≤
          (0 : WithBot ℕ∞) := by sorry
