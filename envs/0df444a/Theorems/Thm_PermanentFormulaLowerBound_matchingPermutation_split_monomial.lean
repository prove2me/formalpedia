-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingPermutation_split_monomial
-- name    : PermanentFormulaLowerBound.matchingPermutation_split_monomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:41.96597+00:00
-- url     : https://prove2.me/theorems/919d0b26-430a-4a1a-b030-9f4f805c5b09
-- title:
--   PermanentFormulaLowerBound.matchingPermutation_split_monomial
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

theorem PermanentFormulaLowerBound.matchingPermutation_split_monomial
    {n : ℕ} {Y : Type u} (d : Y ↪ Fin n × Fin n)
    (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.sumAlgEquiv ℂ Y (matchingOutside d)
        (MvPolynomial.renameEquiv ℂ (matchingVariableEquiv d).symm
          (∏ i : Fin n,
            (MvPolynomial.X (i, σ i) :
              MvPolynomial (Fin n × Fin n) ℂ))) =
      MvPolynomial.monomial (matchingPermutationExponent d σ)
        (matchingPermutationOutsideProduct d σ) := by sorry
