-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingBivariateEvaluationMatrix_eq_kronecker
-- name    : PermanentFormulaLowerBound.matchingBivariateEvaluationMatrix_eq_kronecker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:42.612018+00:00
-- url     : https://prove2.me/theorems/5b766e14-a98d-4cdb-8088-128740ffacaf
-- title:
--   PermanentFormulaLowerBound.matchingBivariateEvaluationMatrix_eq_kronecker
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin

theorem PermanentFormulaLowerBound.matchingBivariateEvaluationMatrix_eq_kronecker
    {F : Type*} [CommRing F] {ell m : ℕ}
    (p q : Fin m → F)
    (P Q : Fin m → Finset (Fin ell)) :
    matchingBivariateEvaluationMatrix p q P Q =
      ((matchingPolynomialEvaluationMatrix p P)ᵀ ⊗ₖ
        (matchingPolynomialEvaluationMatrix q Q)ᵀ).submatrix
          id (Equiv.prodComm (Fin m) (Fin m)) := by sorry
