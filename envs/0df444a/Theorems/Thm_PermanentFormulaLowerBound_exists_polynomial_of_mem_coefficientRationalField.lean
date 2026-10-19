-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_exists_polynomial_of_mem_coefficientRationalField
-- name    : PermanentFormulaLowerBound.exists_polynomial_of_mem_coefficientRationalField
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.96597+00:00
-- url     : https://prove2.me/theorems/9007a2f5-c37c-4261-849c-f60b554c84b4
-- title:
--   PermanentFormulaLowerBound.exists_polynomial_of_mem_coefficientRationalField
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
noncomputable section
variable {F E Y : Type*} [Field F] [Field E] [Algebra F E]

theorem PermanentFormulaLowerBound.exists_polynomial_of_mem_coefficientRationalField
    (s : Finset E) (p : MvPolynomial Y E)
    (hp : algebraMap (MvPolynomial Y E) (FractionRing (MvPolynomial Y E)) p ∈
      coefficientRationalField (F := F) (Y := Y) s) :
    ∃ g : MvPolynomial Y (IntermediateField.adjoin F (s : Set E)),
      MvPolynomial.map
        (algebraMap (IntermediateField.adjoin F (s : Set E)) E) g = p := by sorry
