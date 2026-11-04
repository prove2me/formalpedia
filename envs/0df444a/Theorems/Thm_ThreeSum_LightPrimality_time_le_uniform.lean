-- Prove2me | Theorems.Thm_ThreeSum_LightPrimality_time_le_uniform
-- name    : ThreeSum.LightPrimality.time_le_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:29:22.389392+00:00
-- url     : https://prove2.me/theorems/835bcbcf-3506-43d1-8c95-70a4c7ccc1d5
-- title:
--   Light Primality: time le uniform
-- statement:
--   The Light Primality construction uses the time le uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimality.lean#L85-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimality.lean#L85-L89

import Definitions.Def_Submission_ThreeSum_LightResidues
import Mathlib.Data.Nat.Prime.Basic
import Definitions.Def_Submission_ThreeSum_LightPrimality
set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimality
open Light LightResidues
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem ThreeSum.LightPrimality.time_le_uniform {n maxValue : ℕ} (hn : n ≤ maxValue) :
    time n maxValue ≤ time maxValue maxValue := by sorry
