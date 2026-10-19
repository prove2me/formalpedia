-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMapFiniteGradedQuotient_finrank_eq_sum
-- name    : PermanentRollout.homogeneousMapFiniteGradedQuotient_finrank_eq_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/27d79cd4-4a72-40eb-89d9-33ee94bfb865
-- title:
--   PermanentRollout.homogeneousMapFiniteGradedQuotient_finrank_eq_sum
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra

theorem PermanentRollout.homogeneousMapFiniteGradedQuotient_finrank_eq_sum
    {ι : Type*} [Finite ι] (I : Ideal (MvPolynomial ι ℂ))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι ℂ))
    (N : ℕ)
    (hhigh : ∀ n : ℕ, N ≤ n →
      ∀ p : MvPolynomial ι ℂ, p.IsHomogeneous n → p ∈ I) :
    Module.finrank ℂ (MvPolynomial ι ℂ ⧸ I) =
      ∑ i : Fin N,
        Module.finrank ℂ (homogeneousMapGradedQuotientPiece I i) := by sorry
