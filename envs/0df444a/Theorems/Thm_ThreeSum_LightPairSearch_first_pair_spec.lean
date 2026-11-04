-- Prove2me | Theorems.Thm_ThreeSum_LightPairSearch_first_pair_spec
-- name    : ThreeSum.LightPairSearch.first_pair_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:01:30.348639+00:00
-- url     : https://prove2.me/theorems/cdd9c558-338d-4c45-892d-7e368ef1d8f5
-- title:
--   Light Pair Search: first pair spec
-- statement:
--   Correctness of the finite exhaustive search, including its no-hit case.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPairSearchMain.lean#L62-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPairSearchMain.lean#L62-L82

import Definitions.Def_Submission_ThreeSum_LightPairSearch
import Definitions.Def_Submission_ThreeSum_LightPairSearchMain
set_option autoImplicit false
open ThreeSum ThreeSum.LightPairSearch
open Light
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightPairSearch.first_pair_spec (q : ℕ) (hq : 0<q) (good : ℕ → ℕ → Prop) [DecidableRel good] :
    (first (goodCode q good) (q*q)=0 ↔ ∀ u<q, ∀ v<q, ¬good u v) ∧
    (∀ code, first (goodCode q good) (q*q)=code+1 →
      code/q<q ∧ code%q<q ∧ good (code/q) (code%q) ∧
      ∀ u<q, ∀ v<q, u*q+v<code → ¬good u v) := by sorry
