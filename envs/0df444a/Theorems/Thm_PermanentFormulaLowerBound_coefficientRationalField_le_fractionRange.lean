-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_coefficientRationalField_le_fractionRange
-- name    : PermanentFormulaLowerBound.coefficientRationalField_le_fractionRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.96597+00:00
-- url     : https://prove2.me/theorems/f15f10f3-525b-44c9-ba58-f09fb07ea301
-- title:
--   PermanentFormulaLowerBound.coefficientRationalField_le_fractionRange
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

theorem PermanentFormulaLowerBound.coefficientRationalField_le_fractionRange (s : Finset E) :
    coefficientRationalField (F := F) (Y := Y) s ≤
      (coefficientFractionEmbedding (Y := Y)
        (IntermediateField.adjoin F (s : Set E))).fieldRange := by sorry
