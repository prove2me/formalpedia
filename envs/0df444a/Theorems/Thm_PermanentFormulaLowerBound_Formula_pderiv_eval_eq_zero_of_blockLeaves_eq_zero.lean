-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_Formula_pderiv_eval_eq_zero_of_blockLeaves_eq_zero
-- name    : PermanentFormulaLowerBound.Formula.pderiv_eval_eq_zero_of_blockLeaves_eq_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.318807+00:00
-- url     : https://prove2.me/theorems/2c737e19-027f-4742-8490-5c930b9d6c71
-- title:
--   PermanentFormulaLowerBound.Formula.pderiv_eval_eq_zero_of_blockLeaves_eq_zero
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
open PermanentFormulaLowerBound.Formula

theorem PermanentFormulaLowerBound.Formula.pderiv_eval_eq_zero_of_blockLeaves_eq_zero
    {ι F : Type*} [CommRing F] [DecidableEq ι]
    (f : Formula ι F) (s : Finset ι) (i : ι) (hi : i ∈ s) :
    blockLeaves s f = 0 → MvPolynomial.pderiv i (eval f) = 0 := by sorry
