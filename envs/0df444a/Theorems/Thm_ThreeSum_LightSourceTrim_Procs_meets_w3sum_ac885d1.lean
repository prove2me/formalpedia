-- Prove2me | Theorems.Thm_ThreeSum_LightSourceTrim_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSourceTrim.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:44:15.008221+00:00
-- url     : https://prove2.me/theorems/72df7c41-46c2-4d45-90df-ef4343fe0b46
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceTrim.lean#L76-L233
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceTrim.lean#L76-L233

import Definitions.Def_Submission_ThreeSum_LightSourceRowFlag
import Definitions.Def_Submission_ThreeSum_SourceFlagProduct
import Definitions.Def_Submission_ThreeSum_LightSourceTrim
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_8f9b8fc511f535d5
import Definitions.Def_WeightedCache3SUM_Alias_e80b8f80e26e0eba
import Definitions.Def_WeightedCache3SUM_Alias_d4ec36c7dcd9fa6e

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceTrim
open Light SourceFlagProduct
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceTrim.Procs.meets_w3sum_ac885d1 {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {J L h p cap occ maps candidates histL histR bitBase rowOut work dst U V M K : ℕ}
    (sel candidate bits : ℕ → ℕ) (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hp : 0 < p) (hh : h ≤ L)
    (hocc : occ+J ≤ rowOut) (hmaps : maps+2*L*M ≤ rowOut)
    (hcandidates : candidates+M ≤ rowOut)
    (hleft : histL+K*p ≤ rowOut) (hright : histR+K*p ≤ rowOut)
    (hbits : bitBase+J*L ≤ rowOut) (hrowOut : rowOut+2 ≤ work) (hdst : dst+2 ≤ rowOut)
    (hspace : LightSourceRowFlag.space work L U ≤ lim.space)
    (hword : (LightSourceRowFlag.word L p U V cap : ℤ) ≤ lim.word)
    (hsel : ∀ j < J, sel j < M) (hcandidate : ∀ s < M, candidate s < K)
    (hoccRead : ∀ j < J, μ (occ+j) = (sel j : ℤ))
    (hcandidateRead : ∀ s < M, μ (candidates+s) = (candidate s : ℤ))
    (hbitsRead : ∀ i < J*L, μ (bitBase+i) = (bits i : ℤ))
    (hbitBound : ∀ i < J*L, bits i ≤ 1)
    (hread0 : ∀ s < M, ∀ a < L, μ (maps+2*L*s+a) = (w0 s a : ℤ))
    (hread1 : ∀ s < M, ∀ a < L, μ (maps+2*L*s+L+a) = (w1 s a : ℤ))
    (hbound0 : ∀ s < M, ∀ a < L, w0 s a ≤ U)
    (hbound1 : ∀ s < M, ∀ a < L, w1 s a ≤ U)
    (hcountL : ∀ k < K, ∀ r < p, μ (histL+k*p+r) = (leftCount k r : ℤ))
    (hcountR : ∀ k < K, ∀ r < p, μ (histR+k*p+r) = (rightCount k r : ℤ))
    (hcountBoundL : ∀ k < K, ∀ r < p, leftCount k r ≤ V)
    (hcountBoundR : ∀ k < K, ∀ r < p, rightCount k r ≤ V) :
    Meets lim P pMain d
      [J,L,h,p,cap,occ,maps,candidates,histL,histR,bitBase,rowOut,work,dst]
      μ (time J L U) (fun _ ν =>
        ν dst = (product (rowFlag L h p cap sel candidate bits w0 w1 leftCount) J : ℤ) ∧
        ν (dst+1) = (product (rowFlag L h p cap sel candidate bits w1 w0 rightCount) J : ℤ) ∧
        KeptBut μ ν rowOut dst 2) := by sorry
