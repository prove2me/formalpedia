-- Prove2me | Theorems.Thm_ThreeSum_LightBandRawAStep_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBandRawAStep.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:02:07.96446+00:00
-- url     : https://prove2.me/theorems/442cd746-d66c-4e45-84ce-b52e994ffdc3
-- title:
--   Light Band Raw AStep: meets
-- statement:
--   The Light Band Raw AStep construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAStep.lean#L31-L122
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAStep.lean#L31-L122

import Definitions.Def_Submission_ThreeSum_LightBandRawARow
import Definitions.Def_Submission_ThreeSum_LightBandRawAStep
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_3284ee33b9feff11
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
open ThreeSum ThreeSum.LightBandRawAStep
open Light BandCandidateRows BandRawA
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {src n g owner values owners positions previous capacity : ℕ} {r : Record}

theorem ThreeSum.LightBandRawAStep.meets_w3sum_ac885d1 {pMain pRow pCopy pFill : ℕ}
    (hmain : P[pMain]?=some (body pRow))
    (hrow : P[pRow]?=some (LightBandRawARow.body pCopy pFill))
    (hcopy : P[pCopy]?=some copyBody) (hfill : P[pFill]?=some fillBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth) (hg : 0 < g)
    (hvalid : r.flag=1 → r.a < BandPartition.size n g)
    (hsrc : src+n ≤ values) (hvalues : values+capacity ≤ owners)
    (howners : owners+capacity ≤ positions) (hspace : positions+capacity ≤ lim.space)
    (hfit : previous+(row n g owner r).length ≤ capacity)
    (hword : ((n+g+owner+10 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pMain d [src,n,g,r.flag,r.a,owner,values,owners,positions,previous] μ (time g)
      (fun result ν => result=((previous+(row n g owner r).length : ℕ) : ℤ) ∧
        (∀ j < (row n g owner r).length,
          ν (values+previous+j)=μ (src+BandPartition.start g r.a+j) ∧
          ν (owners+previous+j)=(owner : ℤ) ∧
          ν (positions+previous+j)=((BandPartition.start g r.a+j : ℕ) : ℤ)) ∧
        LightBandRawARow.KeptOthers μ ν (values+previous) (owners+previous)
          (positions+previous) (row n g owner r).length) := by sorry
