-- Prove2me | Theorems.Thm_ThreeSum_LightSourceMaskFlags_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSourceMaskFlags.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:52:39.518967+00:00
-- url     : https://prove2.me/theorems/3392caf7-9189-402c-b261-8277aea9e4fe
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceMaskFlags.lean#L46-L137
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceMaskFlags.lean#L46-L137

import Definitions.Def_Submission_ThreeSum_LightSourceTrim
import Definitions.Def_Submission_ThreeSum_LightSourceMaskFlags
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_8f9b8fc511f535d5
import Definitions.Def_WeightedCache3SUM_Alias_e80b8f80e26e0eba
import Definitions.Def_WeightedCache3SUM_Alias_d4ec36c7dcd9fa6e
import Definitions.Def_WeightedCache3SUM_Alias_b9dca0c4b48e489f

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceMaskFlags
open Light SourceFlagProduct
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceMaskFlags.Procs.meets_w3sum_ac885d1 {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {J L h p cap occ maps candidates histL histR mask dst bitBase rowOut work U V M K : ℕ}
    (sel candidate : ℕ → ℕ) (w0 w1 leftCount rightCount : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*L+3 ≤ lim.depth)
    (hp : 0 < p) (hh : h ≤ L)
    (hocc : occ+J ≤ bitBase) (hmaps : maps+2*L*M ≤ bitBase)
    (hcandidates : candidates+M ≤ bitBase)
    (hleft : histL+K*p ≤ bitBase) (hright : histR+K*p ≤ bitBase)
    (hdst : dst+2 ≤ bitBase) (hbits : bitBase+J*L ≤ rowOut) (hrowOut : rowOut+2 ≤ work)
    (hspace : space work J L U ≤ lim.space)
    (hword : (word J L p U V cap : ℤ) ≤ lim.word) (hmask : mask < 2^(J*L))
    (hsel : ∀ j < J, sel j < M) (hcandidate : ∀ s < M, candidate s < K)
    (hoccRead : ∀ j < J, μ (occ+j) = (sel j : ℤ))
    (hcandidateRead : ∀ s < M, μ (candidates+s) = (candidate s : ℤ))
    (hread0 : ∀ s < M, ∀ a < L, μ (maps+2*L*s+a) = (w0 s a : ℤ))
    (hread1 : ∀ s < M, ∀ a < L, μ (maps+2*L*s+L+a) = (w1 s a : ℤ))
    (hbound0 : ∀ s < M, ∀ a < L, w0 s a ≤ U)
    (hbound1 : ∀ s < M, ∀ a < L, w1 s a ≤ U)
    (hcountL : ∀ k < K, ∀ r < p, μ (histL+k*p+r) = (leftCount k r : ℤ))
    (hcountR : ∀ k < K, ∀ r < p, μ (histR+k*p+r) = (rightCount k r : ℤ))
    (hcountBoundL : ∀ k < K, ∀ r < p, leftCount k r ≤ V)
    (hcountBoundR : ∀ k < K, ∀ r < p, rightCount k r ≤ V) :
    Meets lim P pMain d
      [J,L,h,p,cap,occ,maps,candidates,histL,histR,mask,dst,bitBase,rowOut,work]
      μ (time J L U) (fun _ ν =>
        ν dst = (product (LightSourceTrim.rowFlag L h p cap sel candidate
          (LightMaskBits.bit (J*L) mask) w0 w1 leftCount) J : ℤ) ∧
        ν (dst+1) = (product (LightSourceTrim.rowFlag L h p cap sel candidate
          (LightMaskBits.bit (J*L) mask) w1 w0 rightCount) J : ℤ) ∧
        KeptBut μ ν bitBase dst 2) := by sorry
