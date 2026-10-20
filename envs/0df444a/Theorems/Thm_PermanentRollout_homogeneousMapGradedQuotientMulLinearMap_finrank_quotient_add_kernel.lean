-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousMapGradedQuotientMulLinearMap_finrank_quotient_add_kernel
-- name    : PermanentRollout.homogeneousMapGradedQuotientMulLinearMap_finrank_quotient_add_kernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:35.41423+00:00
-- url     : https://prove2.me/theorems/f13cb825-85ae-432e-8d29-ad2c88a58aa3
-- title:
--   PermanentRollout.homogeneousMapGradedQuotientMulLinearMap_finrank_quotient_add_kernel
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

theorem PermanentRollout.homogeneousMapGradedQuotientMulLinearMap_finrank_quotient_add_kernel
    {ι : Type*} [Finite ι] (I : Ideal (MvPolynomial ι ℂ))
    (f : MvPolynomial ι ℂ) {e : ℕ} (hf : f.IsHomogeneous e) (n : ℕ) :
    Module.finrank ℂ
        (homogeneousMapGradedQuotientPiece I (e + n) ⧸
          LinearMap.range
            (homogeneousMapGradedQuotientMulLinearMap I f hf n)) +
      Module.finrank ℂ (homogeneousMapGradedQuotientPiece I n) =
        Module.finrank ℂ (homogeneousMapGradedQuotientPiece I (e + n)) +
          Module.finrank ℂ
            (LinearMap.ker
              (homogeneousMapGradedQuotientMulLinearMap I f hf n)) := by sorry
