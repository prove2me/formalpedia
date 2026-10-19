-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_vertexCount_eq_leafCount_add_internalGateCount
-- name    : PermanentFormulaLowerBound.RationalFormula.vertexCount_eq_leafCount_add_internalGateCount
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.318807+00:00
-- url     : https://prove2.me/theorems/53502d09-f0c9-466b-a8e9-1253c56ee318
-- title:
--   PermanentFormulaLowerBound.RationalFormula.vertexCount_eq_leafCount_add_internalGateCount
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
variable {ι : Type u} {R : Type v}

theorem PermanentFormulaLowerBound.RationalFormula.vertexCount_eq_leafCount_add_internalGateCount
    (f : RationalFormula ι R) :
    vertexCount f = leafCount f + internalGateCount f := by sorry
