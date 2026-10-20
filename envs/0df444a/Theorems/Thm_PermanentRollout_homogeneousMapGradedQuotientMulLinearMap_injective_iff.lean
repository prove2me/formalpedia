-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMapGradedQuotientMulLinearMap_injective_iff
-- name    : PermanentRollout.homogeneousMapGradedQuotientMulLinearMap_injective_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/dc570af5-c7ea-44a1-896b-3fa4232e1414
-- title:
--   PermanentRollout.homogeneousMapGradedQuotientMulLinearMap_injective_iff
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

theorem PermanentRollout.homogeneousMapGradedQuotientMulLinearMap_injective_iff
    {ι : Type*} (I : Ideal (MvPolynomial ι ℂ))
    (f : MvPolynomial ι ℂ) {e : ℕ} (hf : f.IsHomogeneous e) (n : ℕ) :
    Function.Injective (homogeneousMapGradedQuotientMulLinearMap I f hf n) ↔
      ∀ p : MvPolynomial.homogeneousSubmodule ι ℂ n,
        f * (p : MvPolynomial ι ℂ) ∈ I →
          (p : MvPolynomial ι ℂ) ∈ I := by sorry
