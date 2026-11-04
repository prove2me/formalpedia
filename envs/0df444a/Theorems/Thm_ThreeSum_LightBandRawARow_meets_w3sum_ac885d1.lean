-- Prove2me | Theorems.Thm_ThreeSum_LightBandRawARow_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBandRawARow.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:50:59.314454+00:00
-- url     : https://prove2.me/theorems/c160de25-4d4c-4e2f-9bbe-d07bdc44cbe3
-- title:
--   Light Band Raw ARow: meets
-- statement:
--   The Light Band Raw ARow construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawARow.lean#L32-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawARow.lean#L32-L65

import Definitions.Def_Submission_ThreeSum_BandRawA
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSum_LightBandRawARow
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Theorems.Thm_ThreeSum_LightScaleArray_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawARow
open Light
set_option maxHeartbeats 1400000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {src values owners positions n owner start : ℕ}

theorem ThreeSum.LightBandRawARow.meets_w3sum_ac885d1 {pMain pCopy pFill : ℕ}
    (hmain : P[pMain]?=some (body pCopy pFill))
    (hcopy : P[pCopy]?=some copyBody) (hfill : P[pFill]?=some fillBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hsrc : src+n ≤ values) (hvalues : values+n ≤ owners)
    (howners : owners+n ≤ positions) (hspace : positions+n ≤ lim.space)
    (hstart : start+n ≤ lim.space) :
    Meets lim P pMain d [src,values,owners,positions,n,owner,start] μ (time n)
      (fun _ ν =>
        (∀ j < n, ν (values+j)=μ (src+j) ∧
          ν (owners+j)=(owner : ℤ) ∧ ν (positions+j)=((start+j : ℕ) : ℤ)) ∧
        KeptOthers μ ν values owners positions n) := by sorry
