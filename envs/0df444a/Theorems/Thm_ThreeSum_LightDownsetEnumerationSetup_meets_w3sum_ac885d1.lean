-- Prove2me | Theorems.Thm_ThreeSum_LightDownsetEnumerationSetup_meets_w3sum_ac885d1
-- name    : ThreeSum.LightDownsetEnumerationSetup.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:16:38.774049+00:00
-- url     : https://prove2.me/theorems/b350e5d3-0ef4-4c2f-8891-2ff9a43f7940
-- title:
--   Light Downset Enumeration Setup: meets
-- statement:
--   The Light Downset Enumeration Setup construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetEnumerationSetup.lean#L23-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetEnumerationSetup.lean#L23-L63

import Definitions.Def_Submission_ThreeSum_LightDownsetEnumeration
import Definitions.Def_Submission_ThreeSum_LightDownsetEnumerationSetup
import Definitions.Def_WeightedCache3SUM_Alias_2ae6d2b4167e20c4
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7

set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetEnumerationSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightDownsetEnumerationSetup.meets_w3sum_ac885d1 {pMain pPowers pDownset pEnum : ℕ}
    (hmain : P[pMain]? = some (body pPowers pDownset))
    (hpowers : P[pPowers]? = some powTableBody)
    (hdownset : P[pDownset]? = some (LightDownsetEnumeration.body pEnum))
    (henum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    {μ : ℕ → ℤ} {L cut dst work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hcut : cut ≤ L) (hdst : dst+downsetCap L cut ≤ work)
    (hd : d+L+2 ≤ lim.depth) :
    Meets lim P pMain d [L,cut,dst,work] μ (time L cut)
      (fun r μ' => r = (downsetCap L cut : ℤ) ∧
        SegN μ' dst (enumerateDownset L cut) ∧ Powers μ' work L ∧
        KeptBut μ μ' work dst (downsetCap L cut)) := by sorry
