-- Prove2me | Theorems.Thm_ThreeSum_LightPairSearch_program_meets
-- name    : ThreeSum.LightPairSearch.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:35:00.189019+00:00
-- url     : https://prove2.me/theorems/8169d257-fe92-4a94-9040-e308824871c1
-- title:
--   Light Pair Search: program meets
-- statement:
--   The arbitrary predicate library is physically included in the program.
--   Every call uses its proved execution time and preserves its memory invariant.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPairSearchProgram.lean#L12-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPairSearchProgram.lean#L12-L28

import Definitions.Def_Submission_ThreeSum_LightPairSearchMain
import Definitions.Def_Submission_ThreeSum_LightPairSearchProgram
set_option autoImplicit false
open ThreeSum ThreeSum.LightPairSearch
open Light
variable {lim : Limits}

theorem ThreeSum.LightPairSearch.program_meets (predicates : Program) (pPred : ℕ) {q ctx T d : ℕ}
    (good : ℕ → ℕ → Prop) [DecidableRel good] (I : (ℕ → ℤ) → Prop)
    (hq : 0<q) (μ : ℕ → ℤ) (hI : I μ)
    (hword : ((q*q+q+ctx+20 : ℕ) : ℤ) ≤ lim.word)
    (hd : d+1<lim.depth)
    (hpred : ∀ u<q, ∀ v<q, ∀ ν, I ν → Meets lim predicates pPred (d+2) [u,v,ctx] ν T
      (fun r ξ => r=(if good u v then 1 else 0) ∧ I ξ)) :
    Meets lim (program predicates pPred) (predicates.length+1) d [q,ctx] μ
      (q*q*(T+200)+100)
      (fun r ν => r=(first (goodCode q good) (q*q) : ℤ) ∧ I ν) := by sorry
