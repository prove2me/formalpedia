-- Prove2me | Theorems.Thm_ThreeSum_LightOutputDecodeDivide_reduce_ends_w3sum_ac885d1
-- name    : ThreeSum.LightOutputDecodeDivide.reduce_ends_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:10:00.994297+00:00
-- url     : https://prove2.me/theorems/9a2d21d1-b15e-4c82-925c-c97da7d58721
-- title:
--   Light Output Decode Divide: reduce ends
-- statement:
--   The Light Output Decode Divide construction uses the reduce ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOutputDecodeDivide.lean#L43-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOutputDecodeDivide.lean#L43-L96

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDivide
import Definitions.Def_WeightedCache3SUM_Alias_acc0ea29d744b7ad

set_option autoImplicit false
open ThreeSum ThreeSum.LightOutputDecodeDivide
open Light Light.Emod
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ} {μ ν : ℕ → ℤ} {a Mo V fr : ℕ}

theorem ThreeSum.LightOutputDecodeDivide.reduce_ends_w3sum_ac885d1 (F : Pre lim Mo V fr) (haV : a ≤ V) {t : ℤ}
    (tab : Table μ ν Mo fr (emodRounds a Mo)) :
    Ends lim P d reduce ⟨frame [a,Mo,fr,a,emodRounds a Mo,t,0],ν⟩
      (60*emodRounds a Mo+4)
      (fun σ => σ = ⟨frame [a,Mo,fr,(a%Mo : ℕ),0,t,(a/Mo : ℕ)],ν⟩) := by sorry
