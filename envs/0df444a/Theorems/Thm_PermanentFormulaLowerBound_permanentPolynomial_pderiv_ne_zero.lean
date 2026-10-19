-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_permanentPolynomial_pderiv_ne_zero
-- name    : PermanentFormulaLowerBound.permanentPolynomial_pderiv_ne_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.318807+00:00
-- url     : https://prove2.me/theorems/ee87e46c-90de-4d17-8480-b2e4bd14e6d6
-- title:
--   PermanentFormulaLowerBound.permanentPolynomial_pderiv_ne_zero
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

theorem PermanentFormulaLowerBound.permanentPolynomial_pderiv_ne_zero
    {n : ℕ} (a b : Fin n) :
    MvPolynomial.pderiv (a, b) (permanentPolynomial n) ≠ 0 := by sorry
