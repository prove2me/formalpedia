-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBuild_program_meets
-- name    : ThreeSum.LightSourceBuild.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:03:23.618945+00:00
-- url     : https://prove2.me/theorems/4289df15-aa10-422e-9d9f-b18698e414cf
-- title:
--   Light Source Build: program meets
-- statement:
--   The Light Source Build construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBuild.lean#L116-L139
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBuild.lean#L116-L139

import Definitions.Def_Submission_ThreeSum_LightSourceGather
import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Theorems.Thm_ThreeSum_LightSourceGather_program_meets
import Theorems.Thm_ThreeSum_LightSourceHistogram_program_meets
import Theorems.Thm_ThreeSum_LightSourceResidues_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBuild
open Light
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBuild.program_meets
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
    Meets lim program 0 d [src,N,raw,flags,n,p,m,hist,dst,codes,work,shift]
      μ (time N n p m U D E) (fun _ ν =>
        (∀ i < n, ν (dst+i) = (LightSourceGather.value m endpoint flag
          (fun r => LightHistogram.count
            (fun j => LightSourceResidues.key p m shift (μ (src+j))) r N) i : ℤ)) ∧
        (∀ r < m, ν (hist+r) = (LightHistogram.count
          (fun j => LightSourceResidues.key p m shift (μ (src+j))) r N : ℤ)) ∧
        Kept μ ν hist) := by sorry
