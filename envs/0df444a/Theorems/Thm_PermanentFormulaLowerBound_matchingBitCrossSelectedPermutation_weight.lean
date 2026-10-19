-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingBitCrossSelectedPermutation_weight
-- name    : PermanentFormulaLowerBound.matchingBitCrossSelectedPermutation_weight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:42.612018+00:00
-- url     : https://prove2.me/theorems/e8c799a8-bf09-4f46-a077-c223c8f56eea
-- title:
--   PermanentFormulaLowerBound.matchingBitCrossSelectedPermutation_weight
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

theorem PermanentFormulaLowerBound.matchingBitCrossSelectedPermutation_weight
    {ell m : ℕ} (p q : Fin m → ℂ)
    (de ab : Fin m × Fin m)
    (σ : MatchingBitCrossSelectedPermutation ell m de ab) :
    (∏ i : {i : Fin ((ell + ell) + m) //
        i ≠ (matchingExternalEntry ell m ab.1 ab.2).1.1},
      MvPolynomial.eval (matchingPermanentSpecialization p q)
        (matchingPermutationOutsideFactor
          (matchingDiagonalEmbedding ell m) σ.1.1 i.1)) =
      matchingCrossWeight p q
        (matchingBitSubset ell (de.1 : ℕ))
        (matchingBitSubset ell (de.2 : ℕ)) ab.1 ab.2
        (matchingBitCrossSelectedToCross σ) := by sorry
