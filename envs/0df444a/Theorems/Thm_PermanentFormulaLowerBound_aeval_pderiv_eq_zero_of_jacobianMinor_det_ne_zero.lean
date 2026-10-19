-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_aeval_pderiv_eq_zero_of_jacobianMinor_det_ne_zero
-- name    : PermanentFormulaLowerBound.aeval_pderiv_eq_zero_of_jacobianMinor_det_ne_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.96597+00:00
-- url     : https://prove2.me/theorems/4c12b723-5f4f-4dc5-8f3e-627143a1c346
-- title:
--   PermanentFormulaLowerBound.aeval_pderiv_eq_zero_of_jacobianMinor_det_ne_zero
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
variable {ι : Type u} {κ : Type v} {F : Type w}

theorem PermanentFormulaLowerBound.aeval_pderiv_eq_zero_of_jacobianMinor_det_ne_zero [Field F]
    [Fintype ι] [DecidableEq ι]
    (g : ι → MvPolynomial κ F) (cols : ι → κ)
    (H : MvPolynomial ι F)
    (hdet : (jacobianMinor g cols).det ≠ 0)
    (hH : MvPolynomial.aeval g H = 0) (i : ι) :
    MvPolynomial.aeval g (MvPolynomial.pderiv i H) = 0 := by sorry
