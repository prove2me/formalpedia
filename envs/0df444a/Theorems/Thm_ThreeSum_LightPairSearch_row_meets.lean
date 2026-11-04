-- Prove2me | Theorems.Thm_ThreeSum_LightPairSearch_row_meets
-- name    : ThreeSum.LightPairSearch.row_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:04:59.753203+00:00
-- url     : https://prove2.me/theorems/ab0faa16-2c3a-46e7-9a25-2a26402cce50
-- title:
--   Light Pair Search: row meets
-- statement:
--   The Light Pair Search construction uses the row meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPairSearch.lean#L26-L86
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPairSearch.lean#L26-L86

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_PairFirst
import Definitions.Def_Submission_ThreeSum_LightPairSearch
set_option autoImplicit false
open ThreeSum ThreeSum.LightPairSearch
open Light
set_option maxHeartbeats 300000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightPairSearch.row_meets {pRow pPred q u ctx T d : ℕ}
    (hrow : P[pRow]?=some (rowBody pPred))
    (good : ℕ → ℕ → Prop) [DecidableRel good] (I : (ℕ → ℤ) → Prop)
    (hq : 0<q) (hu : u<q) (μ : ℕ → ℤ) (hI : I μ)
    (hword : ((q*q+q+ctx+20 : ℕ) : ℤ) ≤ lim.word)
    (hd : d<lim.depth)
    (hpred : ∀ v<q, ∀ ν, I ν → Meets lim P pPred (d+1) [u,v,ctx] ν T
      (fun r ξ => r=(if good u v then 1 else 0) ∧ I ξ)) :
    Meets lim P pRow d [q,u,ctx,first (goodCode q good) (u*q)] μ (rowTime q T)
      (fun r ν => r=(first (goodCode q good) ((u+1)*q) : ℤ) ∧ I ν) := by sorry
