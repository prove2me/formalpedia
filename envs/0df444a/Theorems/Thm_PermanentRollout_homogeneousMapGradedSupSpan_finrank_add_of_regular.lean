-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMapGradedSupSpan_finrank_add_of_regular
-- name    : PermanentRollout.homogeneousMapGradedSupSpan_finrank_add_of_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/d4f000ec-050b-45c8-9e3d-a72cb921c84b
-- title:
--   PermanentRollout.homogeneousMapGradedSupSpan_finrank_add_of_regular
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
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra

theorem PermanentRollout.homogeneousMapGradedSupSpan_finrank_add_of_regular
    {ι : Type*} [Finite ι]
    (I : Ideal (MvPolynomial ι ℂ))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι ℂ))
    (f : MvPolynomial ι ℂ) {e : ℕ}
    (hf : f.IsHomogeneous e)
    (hregular : IsSMulRegular (MvPolynomial ι ℂ ⧸ I) f)
    (n : ℕ) :
    Module.finrank ℂ
        (homogeneousMapGradedQuotientPiece
          (I ⊔ Ideal.span {f}) (e + n)) +
      Module.finrank ℂ (homogeneousMapGradedQuotientPiece I n) =
      Module.finrank ℂ
        (homogeneousMapGradedQuotientPiece I (e + n)) := by sorry
