-- Prove2me | Theorems.Thm_ThreeSum_LightRawAKeys_meets_w3sum_ac885d1
-- name    : ThreeSum.LightRawAKeys.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:10:24.276095+00:00
-- url     : https://prove2.me/theorems/7c534ff2-4182-4c05-9d70-f17d4fccb2fe
-- title:
--   Light Raw AKeys: meets
-- statement:
--   The Light Raw AKeys construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRawAKeys.lean#L35-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightRawAKeys.lean#L35-L112

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightRawAKeys
import Definitions.Def_WeightedCache3SUM_Alias_fe1d986d2522f297
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Definitions.Def_WeightedCache3SUM_Alias_375bd97fc128be02
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScaleArray_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightRawAKeys
open Light LightResidues RawIncidences RawAKeyLists
set_option maxHeartbeats 1000000
set_option maxRecDepth 6000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightRawAKeys.meets_w3sum_ac885d1 {pMain pResidues pAffine pEmod src free p U : ℕ} {μ : ℕ → ℤ}
    (hmain : P[pMain]? = some (body pResidues pAffine))
    (hres : P[pResidues]? = some (residuesBody pEmod))
    (haff : P[pAffine]? = some LightReportingAffine.body)
    (hem : P[pEmod]? = some emodBody) (xs : List ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 0 < p)
    (hsrc : src+xs.length ≤ free)
    (hspace : space free xs.length U ≤ lim.space)
    (hword : (word p U : ℤ) ≤ lim.word) (hd : d+2 ≤ lim.depth)
    (hread : Seg μ src xs) (hvalues : ∀ x ∈ xs, |x| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,xs.length,p,free] μ (time xs.length U)
      (fun r ν => r=(free : ℤ) ∧ Seg ν free (keys p xs) ∧ Kept μ ν free) := by sorry
