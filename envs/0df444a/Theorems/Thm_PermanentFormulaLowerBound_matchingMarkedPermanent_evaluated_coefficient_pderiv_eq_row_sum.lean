-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingMarkedPermanent_evaluated_coefficient_pderiv_eq_row_sum
-- name    : PermanentFormulaLowerBound.matchingMarkedPermanent_evaluated_coefficient_pderiv_eq_row_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.96597+00:00
-- url     : https://prove2.me/theorems/71de2337-b826-43fe-b46f-2a24684e6d05
-- title:
--   PermanentFormulaLowerBound.matchingMarkedPermanent_evaluated_coefficient_pderiv_eq_row_sum
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

theorem PermanentFormulaLowerBound.matchingMarkedPermanent_evaluated_coefficient_pderiv_eq_row_sum
    {n : ℕ} {Y : Type u} [DecidableEq Y]
    (d : Y ↪ Fin n × Fin n) (α : Y →₀ ℕ)
    (z : matchingOutside d) (ξ : matchingOutside d → ℂ) :
    MvPolynomial.eval ξ
        (MvPolynomial.pderiv z
          (coefficientPolynomial (matchingMarkedPermanent d) α)) =
      ∑ σ : Equiv.Perm (Fin n),
        if matchingPermutationExponent d σ = α ∧
          σ z.1.1 = z.1.2 then
          ∏ i : {i : Fin n // i ≠ z.1.1},
            MvPolynomial.eval ξ
              (matchingPermutationOutsideFactor d σ i.1)
        else 0 := by sorry
