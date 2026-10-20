-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_yLeafCount_rename_matchingVariableEquiv
-- name    : PermanentFormulaLowerBound.RationalFormula.yLeafCount_rename_matchingVariableEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:42.612018+00:00
-- url     : https://prove2.me/theorems/e4ed8e2a-cca3-4ce3-9a89-18f6bda267cb
-- title:
--   PermanentFormulaLowerBound.RationalFormula.yLeafCount_rename_matchingVariableEquiv
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
variable {ι : Type u} {κ : Type v} {R : Type w}

theorem PermanentFormulaLowerBound.RationalFormula.yLeafCount_rename_matchingVariableEquiv
    {n : ℕ} {Y : Type u} [Fintype Y]
    (d : Y ↪ Fin n × Fin n) (f : RationalFormula (Fin n × Fin n) R) :
    yLeafCount (rename (matchingVariableEquiv d).symm f) =
      blockLeaves (matchingMarkedFinset d) f := by sorry
