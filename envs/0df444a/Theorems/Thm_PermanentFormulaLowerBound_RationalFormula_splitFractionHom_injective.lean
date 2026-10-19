-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_splitFractionHom_injective
-- name    : PermanentFormulaLowerBound.RationalFormula.splitFractionHom_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.318807+00:00
-- url     : https://prove2.me/theorems/f907ccb1-4d8e-4ef8-a715-711c1d645c4f
-- title:
--   PermanentFormulaLowerBound.RationalFormula.splitFractionHom_injective
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
open PermanentFormulaLowerBound.RationalFormula
noncomputable section
variable {Y Z F : Type*}

theorem PermanentFormulaLowerBound.RationalFormula.splitFractionHom_injective [Field F] :
    Function.Injective (splitFractionHom (Y := Y) (Z := Z) (F := F)) := by sorry
