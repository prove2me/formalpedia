-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_bank_exit_meets
-- name    : ThreeSum.LightWeightedFrozenQuery.bank_exit_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:26:57.444144+00:00
-- url     : https://prove2.me/theorems/24eddc92-33e2-4133-a87f-14d3935fe832
-- title:
--   Light Weighted Frozen Query: bank exit meets
-- statement:
--   The bank exit is an actual procedure call to the checked physical lookup.
--   This closes the first base case of the recursive query execution contract.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Frozen.lean#L77-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Frozen.lean#L77-L108

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_Weighted_Frozen
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open Light
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedFrozenQuery.bank_exit_meets {pMain pLookup pSelf pDigit pZero pErase d t : ℕ}
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
