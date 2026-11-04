-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceStages_meets_right
-- name    : ThreeSum.LightBlockSourceStages.meets_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:10:34.850778+00:00
-- url     : https://prove2.me/theorems/b11a15f1-7993-412b-960d-d399336f6f16
-- title:
--   Light Block Source Stages: meets right
-- statement:
--   The Light Block Source Stages construction uses the meets right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceStages.lean#L88-L126
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceStages.lean#L88-L126

import Definitions.Def_Submission_ThreeSum_LightSourceStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBuild
import Definitions.Def_Submission_ThreeSum_BlockSourceTableLayout
import Definitions.Def_Submission_ThreeSum_LightBlockSourceStages
import Theorems.Thm_ThreeSum_LightBlockSourceBuild_meets_right

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceStages
open Light BlockEncoding BlockIndex BlockSourceEncoding GlobalEncoding
open SubsetAddress LightBlockSourceBuild
set_option maxHeartbeats 1800000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightBlockSourceStages.meets_right {β : Type*} [Fintype β] [DecidableEq β] {pMain : ℕ}
    (C : LightSourceStages.Procs P pMain)
    {μ : ℕ → ℤ} {h J src N raw flags p hist base codes work cut maskBase U D : ℕ} {shift : ℤ}
    (B : Finset β) (b : β → ℤ) (q : GlobalOutput h J) (e : Fin N ≃ B)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+8 ≤ lim.depth)
    (hp : 0 < p) (hcut : cut ≤ J*(512*h))
    (hsrc : src+N ≤ hist) (hraw : raw+downsetCap (J*(512*h)) cut ≤ hist)
    (hflags : flags+downsetCap (J*(512*h)) cut ≤ hist)
    (hhist : hist+modulus h J ≤ base)
    (hdata : base+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ maskBase)
    (hmasks : maskBase+downsetCap (J*(512*h)) cut ≤ codes) (hcodes : codes+N ≤ work)
    (hspace : LightSourceStages.space work (J*(512*h)) p U D (endpointBound h J) ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ))
    (hword : (LightSourceStages.word N (J*(512*h)) p (modulus h J) U D (endpointBound h J) : ℤ) ≤ lim.word)
    (hvalues : ∀ i < N, |μ (src+i)| ≤ (U : ℤ))
    (hinput : ∀ i : Fin N, μ (src+i.val) = b (e i))
    (hrawRead : ∀ i < downsetCap (J*(512*h)) cut,
      μ (raw+i) = endpointRight (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i))
    (hflagRead : ∀ i < downsetCap (J*(512*h)) cut,
      μ (flags+i) = (if RightAllowed (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i)
        then 1 else 0 : ℕ)) :
    Meets lim P pMain d
      [src,N,raw,flags,p,modulus h J,hist,base,codes,work,shift,J*(512*h),cut,maskBase,
        downsetCap (J*(512*h)) cut]
      μ (LightSourceStages.time N (J*(512*h)) cut p (modulus h J) U D (endpointBound h J))
      (fun _ ν => LightZetaStages.StoredThrough ν base cut
        (BlockIndexedQuery.rightSource (p : ℤ) shift B b q) (J*(512*h)) ∧ Kept μ ν hist) := by sorry
