-- Prove2me | Theorems.Thm_ThreeSum_LightDownsetEnumeration_meets_w3sum_ac885d1
-- name    : ThreeSum.LightDownsetEnumeration.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:45:25.422373+00:00
-- url     : https://prove2.me/theorems/d41d8751-792d-48b4-8855-37f8d99cc0b7
-- title:
--   Light Downset Enumeration: meets
-- statement:
--   The Light Downset Enumeration construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetEnumeration.lean#L69-L143
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetEnumeration.lean#L69-L143

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightDownsetEnumeration
import Definitions.Def_WeightedCache3SUM_Alias_f29d07b5f5ce2e2c
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7

set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightDownsetEnumeration.meets_w3sum_ac885d1 {pMain pEnum L cut dst powers d : ℕ} {μ : ℕ → ℤ}
    (hmain : P[pMain]? = some (body pEnum))
    (henum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hcut : cut ≤ L) (hdst : dst+downsetCap L cut ≤ powers)
    (hpowers : Powers μ powers L) (hd : d+L+1 ≤ lim.depth) :
    Meets lim P pMain d [L,cut,dst,powers] μ (time L cut)
      (fun r μ' => r = (downsetCap L cut : ℤ) ∧
        SegN μ' dst (enumerateDownset L cut) ∧
        SameOutside μ μ' dst (downsetCap L cut)) := by sorry
