-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingBitCrossSelectedSupportEmbedding_factor
-- name    : PermanentFormulaLowerBound.matchingBitCrossSelectedSupportEmbedding_factor
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:42.612018+00:00
-- url     : https://prove2.me/theorems/84f77117-494b-41a2-b08e-0715049e49ae
-- title:
--   PermanentFormulaLowerBound.matchingBitCrossSelectedSupportEmbedding_factor
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

theorem PermanentFormulaLowerBound.matchingBitCrossSelectedSupportEmbedding_factor
    {ell m : ℕ} (p q : Fin m → ℂ)
    {de ab : Fin m × Fin m}
    (σ : MatchingBitCrossSelectedPermutation ell m de ab)
    (t : ↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
      ↥(matchingBitSubset ell (de.2 : ℕ))) :
    MvPolynomial.eval (matchingPermanentSpecialization p q)
        (matchingPermutationOutsideFactor
          (matchingDiagonalEmbedding ell m) σ.1.1
          (matchingBitCrossSelectedSupportEmbedding σ t)) =
      match t with
      | .inl u =>
          p ((matchingCrossRows
            (matchingBitCrossSelectedToCross σ) (.inl u)).1) ^
              (2 ^ (u.1 : ℕ))
      | .inr v =>
          q ((matchingCrossCols
            (matchingBitCrossSelectedToCross σ) (.inr v)).1) ^
              (2 ^ (v.1 : ℕ)) := by sorry
