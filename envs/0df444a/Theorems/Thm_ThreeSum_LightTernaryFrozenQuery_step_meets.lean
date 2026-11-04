-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_step_meets
-- name    : ThreeSum.LightTernaryFrozenQuery.step_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:32:31.226252+00:00
-- url     : https://prove2.me/theorems/6a7ea865-7db7-4ad0-83cb-908673c93e5b
-- title:
--   Light Ternary Frozen Query: step meets
-- statement:
--   The Light Ternary Frozen Query construction uses the step meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryPrepare.lean#L13-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryPrepare.lean#L13-L77

import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryBranches
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPrepare
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open Light ThreeSum.LightSubsetAddress
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryFrozenQuery.step_meets {pMain pSelf pLookup pDigit pZero pErase d branchTime : ℕ}
    (hmain : P[pMain]? = some (body pSelf pLookup pDigit pZero pErase))
    (hdigit : P[pDigit]? = some (LightTernaryCodes.digitBody pErase))
    (hzero : P[pZero]? = some (LightTernaryCodes.zeroBody pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    (N K rank cut m bankCodes bankCount bankValues nearCodes nearCount nearValues powers L : ℕ)
    (q : Fin 3) (value : ℤ) (μ : ℕ → ℤ)
    (hK : K < N) (hbank : cut < rank)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(2*N+1) ≤ lim.space)
    (hword : ((2^(2*N+1) : ℕ) : ℤ) ≤ lim.word)
    (hNword : 2*(N : ℤ)+3 ≤ lim.word)
    (hcutWord : (cut : ℤ)+1 ≤ lim.word)
    (hpowers : Powers μ powers (2*N)) (hm : m < 2^(2*N))
    (hargs : ∀ x ∈ inputs N (K+1) rank cut m bankCodes bankCount bankValues
      nearCodes nearCount nearValues powers L, |x| ≤ lim.word)
    (hq : LightTernaryCodes.digit (2*N) (2*(N-(K+1))) (2*(N-(K+1))+1) m=q.val)
    (hd : d+2*N+2 ≤ lim.depth)
    (hbranch : Ends lim P d (branches pSelf)
      ⟨frame (preparedInputs N K rank cut m bankCodes bankCount bankValues
        nearCodes nearCount nearValues powers L q
        (LightTernaryCodes.zeroCode (2*N) (2*(N-(K+1))) (2*(N-(K+1))+1) m)
        (LightTernaryCodes.oneCode (2*N) (2*(N-(K+1))+1) m)),μ⟩ branchTime
      (fun σ => σ.loc 0=value ∧ σ.mem=μ)) :
    Meets lim P pMain d (inputs N (K+1) rank cut m bankCodes bankCount bankValues
      nearCodes nearCount nearValues powers L) μ (prepTime N+branchTime)
      (fun v μ' => v=value ∧ μ'=μ) := by sorry
