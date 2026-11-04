-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedEnumerationSetup_meets
-- name    : ThreeSum.LightWeightedEnumerationSetup.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:35.241196+00:00
-- url     : https://prove2.me/theorems/a5f45fe5-246b-43b8-9645-cb97790c4149
-- title:
--   Light Weighted Enumeration Setup: meets
-- statement:
--   The Light Weighted Enumeration Setup construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/EnumerationSetup.lean#L30-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/EnumerationSetup.lean#L30-L76

import Definitions.Def_Submission_Weighted_LightEnumeration
import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_EnumerationSetup
import Theorems.Thm_ThreeSum_LightCacheEnumeration_meets
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedEnumerationSetup
open Light ThreeSum.LightSubsetAddress ThreeSum.WeightedAddresses
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedEnumerationSetup.meets {pMain pPowers pEnum : ℕ}
    (hmain : P[pMain]? = some (body pPowers pEnum))
    (hpowers : P[pPowers]? = some powTableBody)
    (henum : P[pEnum]? = some (LightCacheEnumeration.body pEnum))
    {μ : ℕ → ℤ} {N T dst work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(2*N+1) ≤ lim.space)
    (hword : ((4^(N+1) : ℕ) : ℤ) ≤ lim.word)
    (hcontrol : ((1025*N+1100 : ℕ) : ℤ)≤lim.word)
    (hcut : T ≤ 1025*N) (hdst : dst+(codes N T).length ≤ work)
    (hd : d+N+2 ≤ lim.depth) :
    Meets lim P pMain d [N,T,dst,work] μ (time N T)
      (fun r μ' => r = ((codes N T).length : ℤ) ∧
        Seg μ' dst ((codes N T).map (fun (a : ℕ) => (a : ℤ))) ∧
        Powers μ' work (2*N) ∧ KeptBut μ μ' work dst (codes N T).length) := by sorry
