-- Prove2me | Theorems.Thm_PermanentFormulaLowerBound_matchingWeightedCrossBitPermutation_sum
-- name    : PermanentFormulaLowerBound.matchingWeightedCrossBitPermutation_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:42.612018+00:00
-- url     : https://prove2.me/theorems/632c5de9-318e-4690-83a9-de75401aabe3
-- title:
--   PermanentFormulaLowerBound.matchingWeightedCrossBitPermutation_sum
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

theorem PermanentFormulaLowerBound.matchingWeightedCrossBitPermutation_sum
    {F : Type*} [CommRing F] {ell m : ℕ}
    (p q : Fin m → F) (de ab : Fin m × Fin m) :
    (∑ σ : MatchingCrossPermutation
      (↥(matchingBitSubset ell (de.1 : ℕ)) ⊕
        ↥(matchingBitSubset ell (de.2 : ℕ)))
      {j : Fin m // j ≠ ab.1}
      {j : Fin m // j ≠ ab.2},
        matchingCrossWeight p q
          (matchingBitSubset ell (de.1 : ℕ))
          (matchingBitSubset ell (de.2 : ℕ)) ab.1 ab.2 σ) =
      matchingWeightedBivariateEvaluationMatrix p q
        (fun d : Fin m => matchingBitSubset ell (d : ℕ))
        (fun e : Fin m => matchingBitSubset ell (e : ℕ)) de ab := by sorry
