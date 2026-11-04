-- Prove2me | Theorems.Thm_ThreeSum_LightPairSearch_meets
-- name    : ThreeSum.LightPairSearch.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:31:49.84404+00:00
-- url     : https://prove2.me/theorems/1c4d6fdf-3344-4b0b-8d8e-e923a41fcd79
-- title:
--   Light Pair Search: meets
-- statement:
--   The Light Pair Search construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPairSearchMain.lean#L21-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPairSearchMain.lean#L21-L54

import Definitions.Def_Submission_ThreeSum_LightPairSearch
import Definitions.Def_Submission_ThreeSum_LightPairSearchMain
set_option autoImplicit false
open ThreeSum ThreeSum.LightPairSearch
open Light
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightPairSearch.meets {pMain pRow pPred q ctx T d : ℕ}
    (hmain : P[pMain]?=some (body pRow)) (hrow : P[pRow]?=some (rowBody pPred))
    (good : ℕ → ℕ → Prop) [DecidableRel good] (I : (ℕ → ℤ) → Prop)
    (hq : 0<q) (μ : ℕ → ℤ) (hI : I μ)
    (hword : ((q*q+q+ctx+20 : ℕ) : ℤ) ≤ lim.word)
    (hd : d+1<lim.depth)
    (hpred : ∀ u<q, ∀ v<q, ∀ ν, I ν → Meets lim P pPred (d+2) [u,v,ctx] ν T
      (fun r ξ => r=(if good u v then 1 else 0) ∧ I ξ)) :
    Meets lim P pMain d [q,ctx] μ (time q T)
      (fun r ν => r=(first (goodCode q good) (q*q) : ℤ) ∧ I ν) := by sorry
