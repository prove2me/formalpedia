-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingBivariateEvaluationMatrix_det_ne_zero
-- name    : PermanentFormulaLowerBound.matchingBivariateEvaluationMatrix_det_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:42.612018+00:00
-- url     : https://prove2.me/theorems/c2defc66-93bd-40bc-9097-069790cee6e1
-- title:
--   PermanentFormulaLowerBound.matchingBivariateEvaluationMatrix_det_ne_zero
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

theorem PermanentFormulaLowerBound.matchingBivariateEvaluationMatrix_det_ne_zero
    {F : Type*} [Field F] [CharZero F] {ell m : ℕ}
    (p q : Fin m → F)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (P Q : Fin m → Finset (Fin ell))
    (hP : ∀ d : Fin m, matchingBinaryDegree (P d) = (d : ℕ))
    (hQ : ∀ e : Fin m, matchingBinaryDegree (Q e) = (e : ℕ)) :
    (matchingBivariateEvaluationMatrix p q P Q).det ≠ 0 := by sorry
