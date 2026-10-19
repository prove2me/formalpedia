-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingPermanentJacobian_apply
-- name    : PermanentFormulaLowerBound.matchingPermanentJacobian_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:42.612018+00:00
-- url     : https://prove2.me/theorems/893701cc-37c4-498a-84f1-453e95bf3c40
-- title:
--   PermanentFormulaLowerBound.matchingPermanentJacobian_apply
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

theorem PermanentFormulaLowerBound.matchingPermanentJacobian_apply
    {ell m : ℕ} (p q : Fin m → ℂ)
    (de ab : Fin m × Fin m) :
    matchingPermanentJacobian (ell := ell) p q de ab =
      ∑ σ : Equiv.Perm (Fin ((ell + ell) + m)),
        if matchingPermutationExponent
          (matchingDiagonalEmbedding ell m) σ =
              matchingSquarefreeMonomial
                (matchingBitCoefficientSet ell m de) ∧
          σ (matchingExternalEntry ell m ab.1 ab.2).1.1 =
            (matchingExternalEntry ell m ab.1 ab.2).1.2 then
          ∏ i : {i : Fin ((ell + ell) + m) //
            i ≠ (matchingExternalEntry ell m ab.1 ab.2).1.1},
            MvPolynomial.eval (matchingPermanentSpecialization p q)
              (matchingPermutationOutsideFactor
                (matchingDiagonalEmbedding ell m) σ i.1)
        else 0 := by sorry
