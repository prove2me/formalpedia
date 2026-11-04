-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceBuild_meets_right
-- name    : ThreeSum.LightBlockSourceBuild.meets_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:25.73919+00:00
-- url     : https://prove2.me/theorems/9ff44670-1565-48e7-ac2b-6875df0df6fe
-- title:
--   Light Block Source Build: meets right
-- statement:
--   The Light Block Source Build construction uses the meets right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBuild.lean#L102-L132
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBuild.lean#L102-L132

import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBuild
set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBuild
open Light BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds
set_option maxHeartbeats 1500000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightBlockSourceBuild.meets_right {β : Type*} [DecidableEq β] {pMain : ℕ}
    (S : LightSourceBuild.Procs P pMain)
    {μ : ℕ → ℤ} {h J src N raw flags n p hist dst codes work U D : ℕ} {shift : ℤ}
    (o : Occurrences h J) (C : Finset β) (c : β → ℤ)
    (sets : ℕ → Finset (BlockRows.Coord J (512*h))) (e : Fin N ≃ C)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hp : 0 < p)
    (hsrc : src+N ≤ hist) (hraw : raw+n ≤ hist) (hflags : flags+n ≤ hist)
    (hhist : hist+modulus h J ≤ dst) (hdst : dst+n ≤ codes) (hcodes : codes+N ≤ work)
    (hspace : LightSourceBuild.space work p U D (endpointBound h J) ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ))
    (hword : (LightSourceBuild.word p (modulus h J) U D (endpointBound h J) : ℤ) ≤ lim.word)
    (hvalues : ∀ i < N, |μ (src+i)| ≤ (U : ℤ))
    (hinput : ∀ i : Fin N, μ (src+i.val) = c (e i))
    (hrawRead : ∀ i < n, μ (raw+i) = endpointRight o (sets i))
    (hflagRead : ∀ i < n, μ (flags+i) = (if RightAllowed o (sets i) then 1 else 0 : ℕ)) :
    Meets lim P pMain d [src,N,raw,flags,n,p,modulus h J,hist,dst,codes,work,shift]
      μ (LightSourceBuild.time N n p (modulus h J) U D (endpointBound h J))
      (fun _ ν => (∀ i < n, ν (dst+i) = (rightWeights o (p : ℤ) shift C c (sets i) : ℤ)) ∧
        Kept μ ν hist) := by sorry
