-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_eval_rename_eq_matchingMarkedPermanent
-- name    : PermanentFormulaLowerBound.RationalFormula.eval_rename_eq_matchingMarkedPermanent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:42.612018+00:00
-- url     : https://prove2.me/theorems/bd5c780d-7d9f-4099-a4f9-a48f6cb853b2
-- title:
--   PermanentFormulaLowerBound.RationalFormula.eval_rename_eq_matchingMarkedPermanent
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

theorem PermanentFormulaLowerBound.RationalFormula.eval_rename_eq_matchingMarkedPermanent
    {n : ℕ} {Y : Type u}
    (d : Y ↪ Fin n × Fin n)
    (f : RationalFormula (Fin n × Fin n) ℂ)
    (hf : eval f =
      algebraMap (MvPolynomial (Fin n × Fin n) ℂ)
        (FractionRing (MvPolynomial (Fin n × Fin n) ℂ))
        (permanentPolynomial n)) :
    eval (rename (matchingVariableEquiv d).symm f) =
      algebraMap
        (MvPolynomial (Y ⊕ matchingOutside d) ℂ)
        (FractionRing (MvPolynomial (Y ⊕ matchingOutside d) ℂ))
        (matchingMarkedPermanent d) := by sorry
