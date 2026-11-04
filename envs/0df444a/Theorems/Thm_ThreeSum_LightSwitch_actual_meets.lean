-- Prove2me | Theorems.Thm_ThreeSum_LightSwitch_actual_meets
-- name    : ThreeSum.LightSwitch.actual_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:07:35.981563+00:00
-- url     : https://prove2.me/theorems/a469be2f-5f92-4a66-97e8-a08a472f44b5
-- title:
--   Light Switch: actual meets
-- statement:
--   The Light Switch construction uses the actual meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitch.lean#L104-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitch.lean#L104-L112

import Definitions.Def_Submission_ThreeSum_LightSwitchBounds
import Definitions.Def_Submission_ThreeSum_LightSwitchScalar
import Definitions.Def_Submission_ThreeSum_LightSwitch
set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitch
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {μ : ℕ→ℤ} {J j r q d : ℕ}

theorem ThreeSum.LightSwitch.actual_meets {n j : ℕ} (hj : j ≤ Switch.terminalDepth n)
    (hword : (word (Scales.blockCount (Scales.inputBits n))
      (Switch.residualSize n j) : ℤ) ≤ lim.word) :
    Meets lim program 0 d
      [Scales.blockCount (Scales.inputBits n),j,Switch.residualSize n j] μ
      (time (Switch.residualSize n j))
      (fun result ν => result=(Switch.actualSwitch n j : ℤ) ∧ ν=μ) := by sorry
