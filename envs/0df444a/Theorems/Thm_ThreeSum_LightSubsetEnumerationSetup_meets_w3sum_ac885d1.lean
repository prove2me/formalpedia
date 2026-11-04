-- Prove2me | Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSubsetEnumerationSetup.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:16:09.20855+00:00
-- url     : https://prove2.me/theorems/5f174a60-d3fb-478a-bc8c-d998430a51b7
-- title:
--   Light Subset Enumeration Setup: meets
-- statement:
--   The Light Subset Enumeration Setup construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetEnumerationSetup.lean#L23-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetEnumerationSetup.lean#L23-L66

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7

set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetEnumerationSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightSubsetEnumerationSetup.meets_w3sum_ac885d1 {pMain pPowers pEnum : ℕ}
    (hmain : P[pMain]? = some (body pPowers pEnum))
    (hpowers : P[pPowers]? = some powTableBody)
    (henum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    {μ : ℕ → ℤ} {L k dst work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hk : k ≤ L+1) (hdst : dst+L.choose k ≤ work)
    (hd : d+L+1 ≤ lim.depth) :
    Meets lim P pMain d [L,k,dst,work] μ (time L k)
      (fun r μ' => r = (L.choose k : ℤ) ∧
        SegN μ' dst (enumerateLayer L k) ∧ Powers μ' work L ∧
        KeptBut μ μ' work dst (L.choose k)) := by sorry
