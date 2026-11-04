-- Prove2me | Theorems.Thm_ThreeSum_LightOutputDecodeDivide_meets_w3sum_ac885d1
-- name    : ThreeSum.LightOutputDecodeDivide.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:39:23.459688+00:00
-- url     : https://prove2.me/theorems/8df9ebeb-409c-4749-9c8c-9b716ca0774d
-- title:
--   Light Output Decode Divide: meets
-- statement:
--   The Light Output Decode Divide construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOutputDecodeDivide.lean#L98-L116
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOutputDecodeDivide.lean#L98-L116

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDivide
set_option autoImplicit false
open ThreeSum ThreeSum.LightOutputDecodeDivide
open Light Light.Emod
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ} {μ ν : ℕ → ℤ} {a Mo V fr : ℕ}

theorem ThreeSum.LightOutputDecodeDivide.meets_w3sum_ac885d1 {pMain : ℕ} (hmain : P[pMain]? = some body)
    (F : Pre lim Mo V fr) (haV : a ≤ V) :
    Meets lim P pMain d [a,Mo,fr] μ (time a Mo)
      (fun q ν => q = ((a/Mo : ℕ) : ℤ) ∧ Kept μ ν fr) := by sorry
