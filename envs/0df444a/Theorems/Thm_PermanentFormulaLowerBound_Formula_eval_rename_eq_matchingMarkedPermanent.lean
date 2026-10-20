-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_Formula_eval_rename_eq_matchingMarkedPermanent
-- name    : PermanentFormulaLowerBound.Formula.eval_rename_eq_matchingMarkedPermanent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:42.612018+00:00
-- url     : https://prove2.me/theorems/3d80c924-90bf-43a8-a406-2aaf4f5afc6a
-- title:
--   PermanentFormulaLowerBound.Formula.eval_rename_eq_matchingMarkedPermanent
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
variable {ι : Type u} {κ : Type v} {R : Type w}

theorem PermanentFormulaLowerBound.Formula.eval_rename_eq_matchingMarkedPermanent
    {n : ℕ} {Y : Type u}
    (d : Y ↪ Fin n × Fin n) (f : Formula (Fin n × Fin n) ℂ)
    (hf : eval f = permanentPolynomial n) :
    eval (rename (matchingVariableEquiv d).symm f) =
      matchingMarkedPermanent d := by sorry
