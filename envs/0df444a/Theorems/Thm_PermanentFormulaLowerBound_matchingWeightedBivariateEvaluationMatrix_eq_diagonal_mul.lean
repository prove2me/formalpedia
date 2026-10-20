-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingWeightedBivariateEvaluationMatrix_eq_diagonal_mul
-- name    : PermanentFormulaLowerBound.matchingWeightedBivariateEvaluationMatrix_eq_diagonal_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:42.612018+00:00
-- url     : https://prove2.me/theorems/63a7a9af-247d-42f4-851e-75a3fe406bda
-- title:
--   PermanentFormulaLowerBound.matchingWeightedBivariateEvaluationMatrix_eq_diagonal_mul
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

theorem PermanentFormulaLowerBound.matchingWeightedBivariateEvaluationMatrix_eq_diagonal_mul
    {F : Type*} [CommRing F] {ell m : ℕ}
    (p q : Fin m → F)
    (P Q : Fin m → Finset (Fin ell)) :
    matchingWeightedBivariateEvaluationMatrix p q P Q =
      Matrix.diagonal
        (fun de : Fin m × Fin m =>
          (matchingJacobianWeight m (P de.1).card (Q de.2).card : F)) *
        matchingBivariateEvaluationMatrix p q P Q := by sorry
