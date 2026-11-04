-- Prove2me | Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets
-- name    : ThreeSum.LightOutputDecodeDivide.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:39:36.335339+00:00
-- url     : https://prove2.me/theorems/03cac596-d726-4462-b5a0-6fd6c3b7d9b9
-- title:
--   Light Output Decode Divide: program meets
-- statement:
--   The Light Output Decode Divide construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOutputDecodeDivide.lean#L131-L133
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOutputDecodeDivide.lean#L131-L133

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDivide
set_option autoImplicit false
open ThreeSum ThreeSum.LightOutputDecodeDivide
open Light Light.Emod
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ} {μ ν : ℕ → ℤ} {a Mo V fr : ℕ}

theorem ThreeSum.LightOutputDecodeDivide.program_meets (F : Pre lim Mo V fr) (haV : a ≤ V) :
    Meets lim program 0 d [a,Mo,fr] μ (budget V)
      (fun q ν => q = ((a/Mo : ℕ) : ℤ) ∧ Kept μ ν fr) := by sorry
