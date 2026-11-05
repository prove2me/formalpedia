-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedFrozenQuery_step_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery.step_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:09:10.606413+00:00
-- url     : https://prove2.me/theorems/0b8a4b53-5768-4530-b781-b12e201b6d22
-- title:
--   step_meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrozenPrepare.lean#L19-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/FrozenPrepare.lean#L19-L83

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenBranches
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenPrepare
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery
open Light ThreeSum.LightSubsetAddress
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedFrozenQuery.step_meets {pMain pSelf pLookup pDigit pZero pErase d branchTime : ℕ}
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
