-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_blockLeaves_pos_of_eval_eq_permanent
-- name    : PermanentFormulaLowerBound.RationalFormula.blockLeaves_pos_of_eval_eq_permanent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.235103+00:00
-- url     : https://prove2.me/theorems/2a8dcabe-cf8d-4000-a8c3-8ba05dd904d9
-- title:
--   PermanentFormulaLowerBound.RationalFormula.blockLeaves_pos_of_eval_eq_permanent
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

theorem PermanentFormulaLowerBound.RationalFormula.blockLeaves_pos_of_eval_eq_permanent
    {n : ℕ} (f : RationalFormula (Fin n × Fin n) ℂ)
    (hf : eval f =
      algebraMap (MvPolynomial (Fin n × Fin n) ℂ)
        (FractionRing (MvPolynomial (Fin n × Fin n) ℂ))
        (permanentPolynomial n))
    (s : Finset (Fin n × Fin n)) (a b : Fin n)
    (hab : (a, b) ∈ s) :
    0 < blockLeaves s f := by sorry
