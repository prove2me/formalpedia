-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_coefficient_mem_coefficientField
-- name    : PermanentFormulaLowerBound.coefficient_mem_coefficientField
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.96597+00:00
-- url     : https://prove2.me/theorems/fe8db9da-d876-42bd-9209-6a9cdac4181b
-- title:
--   PermanentFormulaLowerBound.coefficient_mem_coefficientField
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
variable {Y : Type u} {Z : Type v} {F : Type w} [Field F]

theorem PermanentFormulaLowerBound.coefficient_mem_coefficientField
    (f : MvPolynomial (Y ⊕ Z) F) (α : Y →₀ ℕ) :
    algebraMap (MvPolynomial Z F) (FractionRing (MvPolynomial Z F))
        (coefficientPolynomial f α) ∈ coefficientField f := by sorry
