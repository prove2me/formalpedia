-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_eval_rename
-- name    : PermanentFormulaLowerBound.RationalFormula.eval_rename
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:42.612018+00:00
-- url     : https://prove2.me/theorems/2c0ca144-457d-44b9-8b89-6f14da955589
-- title:
--   PermanentFormulaLowerBound.RationalFormula.eval_rename
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

theorem PermanentFormulaLowerBound.RationalFormula.eval_rename [Field R] (e : ι ≃ κ)
    (f : RationalFormula ι R) :
    eval (rename e f) = renameFractionEquiv e (eval f) := by sorry
