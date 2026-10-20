-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingMarkedPermanent_split_eq_sum
-- name    : PermanentFormulaLowerBound.matchingMarkedPermanent_split_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.96597+00:00
-- url     : https://prove2.me/theorems/b97da5b1-34ef-468f-842d-d98faf71f12a
-- title:
--   PermanentFormulaLowerBound.matchingMarkedPermanent_split_eq_sum
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

theorem PermanentFormulaLowerBound.matchingMarkedPermanent_split_eq_sum
    {n : ℕ} {Y : Type u} (d : Y ↪ Fin n × Fin n) :
    MvPolynomial.sumAlgEquiv ℂ Y (matchingOutside d)
        (matchingMarkedPermanent d) =
      ∑ σ : Equiv.Perm (Fin n),
        MvPolynomial.monomial (matchingPermutationExponent d σ)
          (matchingPermutationOutsideProduct d σ) := by sorry
