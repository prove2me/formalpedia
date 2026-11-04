-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_memo_exit_meets
-- name    : ThreeSum.LightTernaryFrozenQuery.memo_exit_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:32:09.399885+00:00
-- url     : https://prove2.me/theorems/f33170ea-c106-4c11-b13c-3464e975cc7c
-- title:
--   Light Ternary Frozen Query: memo exit meets
-- statement:
--   The outside-bank terminal exit loads the full product from the near memo.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQuery.lean#L106-L139
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQuery.lean#L106-L139

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQuery
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open Light
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryFrozenQuery.memo_exit_meets {pMain pLookup pSelf pDigit pZero pErase d t : ℕ}
    (hmain : P[pMain]? = some (body pSelf pLookup pDigit pZero pErase))
    (N rank cut bankCodes bankCount bankValues nearCodes nearCount nearValues powers L : ℕ)
    (code value : ℤ) (μ : ℕ → ℤ) (hbank : cut < rank)
    (hone : 1 ≤ lim.word)
    (hcutWord : (cut : ℤ)+1 ≤ lim.word)
    (hargs : ∀ x ∈ inputs N 0 rank cut code bankCodes bankCount bankValues
      nearCodes nearCount nearValues powers L, |x| ≤ lim.word)
    (hd : d+1 ≤ lim.depth)
    (hlookup : Meets lim P pLookup (d+1)
      [nearCodes,nearCount,code,nearValues,powers,L,0] μ t
      (fun r μ' => r=value ∧ μ'=μ)) :
    Meets lim P pMain d (inputs N 0 rank cut code bankCodes bankCount bankValues
      nearCodes nearCount nearValues powers L) μ (t+100)
      (fun r μ' => r=value ∧ μ'=μ) := by sorry
