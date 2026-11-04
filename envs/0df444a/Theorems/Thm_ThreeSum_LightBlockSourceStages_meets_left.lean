-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceStages_meets_left
-- name    : ThreeSum.LightBlockSourceStages.meets_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:10:45.751679+00:00
-- url     : https://prove2.me/theorems/83a66876-44a5-495c-95c5-3e0ea3ebb6af
-- title:
--   Light Block Source Stages: meets left
-- statement:
--   The Light Block Source Stages construction uses the meets left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceStages.lean#L49-L86
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceStages.lean#L49-L86

import Definitions.Def_Submission_ThreeSum_LightSourceStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceBuild
import Definitions.Def_Submission_ThreeSum_BlockSourceTableLayout
import Definitions.Def_Submission_ThreeSum_LightBlockSourceStages
import Theorems.Thm_ThreeSum_LightBlockSourceBuild_meets_left

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceStages
open Light BlockEncoding BlockIndex BlockSourceEncoding GlobalEncoding
open SubsetAddress LightBlockSourceBuild
set_option maxHeartbeats 1800000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightBlockSourceStages.meets_left {β : Type*} [Fintype β] [DecidableEq β] {pMain : ℕ}
    (C : LightSourceStages.Procs P pMain)
    {μ : ℕ → ℤ} {h J src N raw flags p hist base codes work cut maskBase U : ℕ}
    (B : Finset β) (b : β → ℤ) (q : GlobalOutput h J) (e : Fin N ≃ B)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+8 ≤ lim.depth)
    (hp : 0 < p) (hcut : cut ≤ J*(512*h))
    (hsrc : src+N ≤ hist) (hraw : raw+downsetCap (J*(512*h)) cut ≤ hist)
    (hflags : flags+downsetCap (J*(512*h)) cut ≤ hist)
    (hhist : hist+modulus h J ≤ base)
    (hdata : base+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ maskBase)
    (hmasks : maskBase+downsetCap (J*(512*h)) cut ≤ codes) (hcodes : codes+N ≤ work)
    (hspace : LightSourceStages.space work (J*(512*h)) p U 0 (endpointBound h J) ≤ lim.space)
    (hword : (LightSourceStages.word N (J*(512*h)) p (modulus h J) U 0 (endpointBound h J) : ℤ) ≤ lim.word)
    (hvalues : ∀ i < N, |μ (src+i)| ≤ (U : ℤ))
    (hinput : ∀ i : Fin N, μ (src+i.val) = b (e i))
    (hrawRead : ∀ i < downsetCap (J*(512*h)) cut,
      μ (raw+i) = endpointLeft (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i))
    (hflagRead : ∀ i < downsetCap (J*(512*h)) cut,
      μ (flags+i) = (if LeftAllowed (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i)
        then 1 else 0 : ℕ)) :
    Meets lim P pMain d
      [src,N,raw,flags,p,modulus h J,hist,base,codes,work,0,J*(512*h),cut,maskBase,
        downsetCap (J*(512*h)) cut]
      μ (LightSourceStages.time N (J*(512*h)) cut p (modulus h J) U 0 (endpointBound h J))
      (fun _ ν => LightZetaStages.StoredThrough ν base cut
        (BlockIndexedQuery.leftSource (p : ℤ) B b q) (J*(512*h)) ∧ Kept μ ν hist) := by sorry
