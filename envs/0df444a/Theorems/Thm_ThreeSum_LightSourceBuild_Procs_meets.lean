-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBuild_Procs_meets
-- name    : ThreeSum.LightSourceBuild.Procs.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:00:38.116076+00:00
-- url     : https://prove2.me/theorems/bfb17155-9399-49a8-9857-b9f35518c336
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBuild.lean#L43-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBuild.lean#L43-L107

import Definitions.Def_Submission_ThreeSum_LightSourceGather
import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Definitions.Def_WeightedCache3SUM_Alias_27f79aa230fbddf9
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Theorems.Thm_ThreeSum_LightSourceResidues_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBuild
open Light
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBuild.Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {src N raw flags n p m hist dst codes work U D E : ℕ} {shift : ℤ}
    (endpoint : ℕ → ℤ) (flag : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hp : 0 < p) (hm : 0 < m)
    (hsrc : src+N ≤ hist) (hraw : raw+n ≤ hist) (hflags : flags+n ≤ hist)
    (hhist : hist+m ≤ dst) (hdst : dst+n ≤ codes) (hcodes : codes+N ≤ work)
    (hspace : space work p U D E ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (word p m U D E : ℤ) ≤ lim.word)
    (hvalues : ∀ i < N, |μ (src+i)| ≤ (U : ℤ))
    (hrawRead : ∀ i < n, μ (raw+i) = endpoint i)
    (hrawBound : ∀ i < n, |endpoint i| ≤ (E : ℤ))
    (hflagRead : ∀ i < n, μ (flags+i) = (flag i : ℤ))
    (hflagBound : ∀ i < n, flag i ≤ 1) :
    Meets lim P pMain d [src,N,raw,flags,n,p,m,hist,dst,codes,work,shift]
      μ (time N n p m U D E) (fun _ ν =>
        (∀ i < n, ν (dst+i) = (LightSourceGather.value m endpoint flag
          (fun r => LightHistogram.count
            (fun j => LightSourceResidues.key p m shift (μ (src+j))) r N) i : ℤ)) ∧
        (∀ r < m, ν (hist+r) = (LightHistogram.count
          (fun j => LightSourceResidues.key p m shift (μ (src+j))) r N : ℤ)) ∧
        Kept μ ν hist) := by sorry
