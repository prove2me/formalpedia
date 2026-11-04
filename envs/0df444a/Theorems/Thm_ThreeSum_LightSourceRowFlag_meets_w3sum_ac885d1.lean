-- Prove2me | Theorems.Thm_ThreeSum_LightSourceRowFlag_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSourceRowFlag.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:15:13.20918+00:00
-- url     : https://prove2.me/theorems/c34f70c0-5445-413e-a8e0-2d064080e17d
-- title:
--   Light Source Row Flag: meets
-- statement:
--   The Light Source Row Flag construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceRowFlag.lean#L50-L162
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceRowFlag.lean#L50-L162

import Definitions.Def_Submission_ThreeSum_LightSourceRowScan
import Definitions.Def_Submission_ThreeSum_LightSourceFlagTest
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightSourceRowFlag
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_8f9b8fc511f535d5
import Definitions.Def_WeightedCache3SUM_Alias_d4ec36c7dcd9fa6e

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceRowFlag
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceRowFlag.meets_w3sum_ac885d1 {pMain pRow pEmod pFlag : ℕ}
    (hmain : P[pMain]? = some (body pRow pEmod pFlag))
    (hrow : P[pRow]? = some LightSourceRowScan.body)
    (hem : P[pEmod]? = some emodBody)
    (hflag : P[pFlag]? = some LightSourceFlagTest.body)
    {μ : ℕ → ℤ} {src src0 src1 L h histL histR p cap dst work U V : ℕ}
    (bits w0 w1 leftCount rightCount : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hp : 0 < p) (hh : h ≤ L)
    (hsrc : src+L ≤ work) (hsrc0 : src0+L ≤ work) (hsrc1 : src1+L ≤ work)
    (hleft : histL+p ≤ work) (hright : histR+p ≤ work) (hdst : dst+2 ≤ work)
    (hspace : space work L U ≤ lim.space) (hword : (word L p U V cap : ℤ) ≤ lim.word)
    (hbits : ∀ i < L, μ (src+i) = (bits i : ℤ))
    (hread0 : ∀ i < L, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1+i) = (w1 i : ℤ))
    (hbitBound : ∀ i < L, bits i ≤ 1)
    (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U)
    (hcountL : ∀ r < p, μ (histL+r) = (leftCount r : ℤ))
    (hcountR : ∀ r < p, μ (histR+r) = (rightCount r : ℤ))
    (hcountBoundL : ∀ r < p, leftCount r ≤ V)
    (hcountBoundR : ∀ r < p, rightCount r ≤ V) :
    Meets lim P pMain d [src,src0,src1,L,h,histL,histR,p,cap,dst,work] μ (time L U)
      (fun _ ν => ν dst = (flag L h p cap bits w0 w1 leftCount : ℤ) ∧
        ν (dst+1) = (flag L h p cap bits w1 w0 rightCount : ℤ) ∧
        KeptBut μ ν work dst 2) := by sorry
