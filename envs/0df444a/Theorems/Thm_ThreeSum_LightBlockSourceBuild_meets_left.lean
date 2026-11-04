-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceBuild_meets_left
-- name    : ThreeSum.LightBlockSourceBuild.meets_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:54:31.016209+00:00
-- url     : https://prove2.me/theorems/acd4f11c-ab5c-4759-9721-f13f758cc41f
-- title:
--   Light Block Source Build: meets left
-- statement:
--   The Light Block Source Build construction uses the meets left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBuild.lean#L71-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceBuild.lean#L71-L100

import Definitions.Def_Submission_ThreeSum_LightSourceBuild
import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBuild
set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceBuild
open Light BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds
set_option maxHeartbeats 1500000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightBlockSourceBuild.meets_left {β : Type*} [DecidableEq β] {pMain : ℕ}
    (S : LightSourceBuild.Procs P pMain)
    {μ : ℕ → ℤ} {h J src N raw flags n p hist dst codes work U : ℕ}
    (o : Occurrences h J) (B : Finset β) (b : β → ℤ)
    (sets : ℕ → Finset (BlockRows.Coord J (512*h))) (e : Fin N ≃ B)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hp : 0 < p)
    (hsrc : src+N ≤ hist) (hraw : raw+n ≤ hist) (hflags : flags+n ≤ hist)
    (hhist : hist+modulus h J ≤ dst) (hdst : dst+n ≤ codes) (hcodes : codes+N ≤ work)
    (hspace : LightSourceBuild.space work p U 0 (endpointBound h J) ≤ lim.space)
    (hword : (LightSourceBuild.word p (modulus h J) U 0 (endpointBound h J) : ℤ) ≤ lim.word)
    (hvalues : ∀ i < N, |μ (src+i)| ≤ (U : ℤ))
    (hinput : ∀ i : Fin N, μ (src+i.val) = b (e i))
    (hrawRead : ∀ i < n, μ (raw+i) = endpointLeft o (sets i))
    (hflagRead : ∀ i < n, μ (flags+i) = (if LeftAllowed o (sets i) then 1 else 0 : ℕ)) :
    Meets lim P pMain d [src,N,raw,flags,n,p,modulus h J,hist,dst,codes,work,0]
      μ (LightSourceBuild.time N n p (modulus h J) U 0 (endpointBound h J))
      (fun _ ν => (∀ i < n, ν (dst+i) = (leftWeights o (p : ℤ) B b (sets i) : ℤ)) ∧
        Kept μ ν hist) := by sorry
