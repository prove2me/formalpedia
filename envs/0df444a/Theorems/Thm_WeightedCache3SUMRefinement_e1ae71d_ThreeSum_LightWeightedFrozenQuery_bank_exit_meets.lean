-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedFrozenQuery_bank_exit_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery.bank_exit_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:07:01.524552+00:00
-- url     : https://prove2.me/theorems/230c199b-998c-4ce4-9a4f-b9250ece5999
-- title:
--   bank_exit_meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Frozen.lean#L77-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Frozen.lean#L77-L108

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Frozen
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery
open Light
variable {lim : Limits} {P : Program}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery.bank_exit_meets {pMain pLookup pSelf pDigit pZero pErase d t : ℕ}
    (hmain : P[pMain]? = some (body pSelf pLookup pDigit pZero pErase))
    (N K rank cut bankCodes bankCount bankValues nearCodes nearCount nearValues powers L : ℕ)
    (code value : ℤ) (μ : ℕ → ℤ) (hbank : rank ≤ cut)
    (hone : 1 ≤ lim.word)
    (hcutWord : (cut : ℤ)+1 ≤ lim.word)
    (hargs : ∀ x ∈ inputs N K rank cut code bankCodes bankCount bankValues
      nearCodes nearCount nearValues powers L, |x| ≤ lim.word)
    (hd : d+1 ≤ lim.depth)
    (hlookup : Meets lim P pLookup (d+1)
      [bankCodes,bankCount,code,bankValues,powers,L,K] μ t
      (fun r μ' => r=value ∧ μ'=μ)) :
    Meets lim P pMain d (inputs N K rank cut code bankCodes bankCount bankValues
      nearCodes nearCount nearValues powers L) μ (t+80)
      (fun r μ' => r=value ∧ μ'=μ) := by sorry
