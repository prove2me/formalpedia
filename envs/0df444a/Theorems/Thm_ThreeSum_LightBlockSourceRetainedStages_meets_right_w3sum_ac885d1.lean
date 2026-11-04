-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceRetainedStages_meets_right_w3sum_ac885d1
-- name    : ThreeSum.LightBlockSourceRetainedStages.meets_right_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:22:11.74577+00:00
-- url     : https://prove2.me/theorems/d39a194f-d7bf-4951-8fc7-acce9748dda4
-- title:
--   Light Block Source Retained Stages: meets right
-- statement:
--   The Light Block Source Retained Stages construction uses the meets right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceRetainedStages.lean#L90-L125
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceRetainedStages.lean#L90-L125

import Definitions.Def_Submission_ThreeSum_LightSourceRetainedStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceStages
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedStages
import Theorems.Thm_ThreeSum_LightBlockSourceBuild_meets_right
import Theorems.Thm_ThreeSum_LightBlockSourceStages_meets_right

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceRetainedStages
open Light BlockEncoding BlockIndex BlockSourceEncoding GlobalEncoding
open SubsetAddress LightBlockSourceBuild
set_option maxHeartbeats 1800000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightBlockSourceRetainedStages.meets_right_w3sum_ac885d1 {β : Type*} [Fintype β] [DecidableEq β] {pMain : ℕ}
    (C : LightSourceRetainedStages.Procs P pMain)
    {μ : ℕ → ℤ} {h J N raw flags p table base work cut maskBase : ℕ} {shift : ℤ}
    (B : Finset β) (b : β → ℤ) (q : GlobalOutput h J) (v : ℕ → ℤ) (e : Fin N ≃ B)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+8 ≤ lim.depth)
    (hcut : cut ≤ J*(512*h))
    (hraw : raw+downsetCap (J*(512*h)) cut ≤ base)
    (hflags : flags+downsetCap (J*(512*h)) cut ≤ base)
    (htable : table+modulus h J ≤ base)
    (hdata : base+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ maskBase)
    (hmasks : maskBase+downsetCap (J*(512*h)) cut ≤ work)
    (hspace : LightSourceRetainedStages.space work (J*(512*h)) (endpointBound h J) ≤ lim.space)
    (hword : (LightSourceRetainedStages.word (J*(512*h)) (modulus h J) (endpointBound h J) N : ℤ) ≤ lim.word)
    (hinput : ∀ i : Fin N, v i.val = b (e i))
    (hhistRead : ∀ r < modulus h J, μ (table+r) = (histogram p (modulus h J) shift v N r : ℤ))
    (hrawRead : ∀ i < downsetCap (J*(512*h)) cut,
      μ (raw+i) = endpointRight (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i))
    (hflagRead : ∀ i < downsetCap (J*(512*h)) cut,
      μ (flags+i) = (if RightAllowed (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i)
        then 1 else 0 : ℕ)) :
    Meets lim P pMain d
      [raw,flags,table,base,modulus h J,work,J*(512*h),cut,maskBase,downsetCap (J*(512*h)) cut]
      μ (LightSourceRetainedStages.time (J*(512*h)) cut (endpointBound h J))
      (fun _ ν => LightZetaStages.StoredThrough ν base cut
        (BlockIndexedQuery.rightSource (p : ℤ) shift B b q) (J*(512*h)) ∧ Kept μ ν base) := by sorry
