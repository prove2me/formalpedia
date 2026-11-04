-- Prove2me | Theorems.Thm_ThreeSum_LightSubsetSetup_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSubsetSetup.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:16:07.11967+00:00
-- url     : https://prove2.me/theorems/675d9e82-db06-4851-8a95-542897db486e
-- title:
--   Light Subset Setup: meets
-- statement:
--   The Light Subset Setup construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetSetup.lean#L36-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetSetup.lean#L36-L78

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSubsetSetup.meets_w3sum_ac885d1 {pMain pBuild pFill pRow pLinear pPowers pRank : ℕ}
    (C : Procs P pMain pBuild pFill pRow pLinear pPowers pRank)
    {μ : ℕ → ℤ} {L k m work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hm : IsMask L k m) (hd : d+L+3 ≤ lim.depth) :
    Meets lim P pMain d [L,k,m,work] μ (time L)
      (fun r μ' => r = (layerRank L k m : ℤ) ∧ Table μ' work L ∧
        Powers μ' (work+tableSize L) L ∧ Kept μ μ' work) := by sorry
