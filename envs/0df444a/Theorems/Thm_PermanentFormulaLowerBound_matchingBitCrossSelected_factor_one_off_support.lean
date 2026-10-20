-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingBitCrossSelected_factor_one_off_support
-- name    : PermanentFormulaLowerBound.matchingBitCrossSelected_factor_one_off_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:42.612018+00:00
-- url     : https://prove2.me/theorems/0c0d1f99-6d48-4116-b840-f9d8eab65d23
-- title:
--   PermanentFormulaLowerBound.matchingBitCrossSelected_factor_one_off_support
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

theorem PermanentFormulaLowerBound.matchingBitCrossSelected_factor_one_off_support
    {ell m : ℕ} (p q : Fin m → ℂ)
    (de ab : Fin m × Fin m)
    (σ : MatchingBitCrossSelectedPermutation ell m de ab)
    (i : Fin ((ell + ell) + m))
    (hP : ∀ u : ↥(matchingBitSubset ell (de.1 : ℕ)),
      i ≠ matchingBlockIndexEquiv ell m (.inl (.inl u.1)))
    (hQ : ∀ v : ↥(matchingBitSubset ell (de.2 : ℕ)),
      i ≠ σ.1.1.symm
        (matchingBlockIndexEquiv ell m (.inl (.inr v.1)))) :
    MvPolynomial.eval (matchingPermanentSpecialization p q)
      (matchingPermutationOutsideFactor (matchingDiagonalEmbedding ell m)
        σ.1.1 i) = 1 := by sorry
