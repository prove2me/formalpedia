-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_coefficientPolynomial_rename_outside
-- name    : PermanentFormulaLowerBound.coefficientPolynomial_rename_outside
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.235103+00:00
-- url     : https://prove2.me/theorems/223b9a27-f1aa-4c43-916e-240074c0ce03
-- title:
--   PermanentFormulaLowerBound.coefficientPolynomial_rename_outside
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

theorem PermanentFormulaLowerBound.coefficientPolynomial_rename_outside
    {Y : Type u} {Z : Type v} {W : Type w}
    {F : Type*} [Field F]
    (e : Z ≃ W) (f : MvPolynomial (Y ⊕ Z) F)
    (α : Y →₀ ℕ) :
    coefficientPolynomial
        (MvPolynomial.renameEquiv F
          (Equiv.sumCongr (Equiv.refl Y) e) f) α =
      MvPolynomial.renameEquiv F e (coefficientPolynomial f α) := by sorry
