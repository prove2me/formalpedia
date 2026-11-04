-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFixedChannelLoop_arguments_spec
-- name    : ThreeSum.LightTernaryFixedChannelLoop.arguments_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:58.852619+00:00
-- url     : https://prove2.me/theorems/13bb6444-5b4a-4f11-9a42-ced1c8bea654
-- title:
--   Light Ternary Fixed Channel Loop: arguments spec
-- statement:
--   The Light Ternary Fixed Channel Loop construction uses the arguments spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFixedChannelLoop.lean#L14-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFixedChannelLoop.lean#L14-L34

import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_Submission_ThreeSum_LightTernaryFixedChannelLoop
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFixedChannelLoop
open Light
set_option maxHeartbeats 1500000

theorem ThreeSum.LightTernaryFixedChannelLoop.arguments_spec {lim : Limits} {loc μ : ℕ→ℤ} (vals : List ℤ)
    (hloc : ∀ i<vals.length, loc i=frame vals i) :
    (∀ e∈arguments vals.length, e.Safe lim ⟨loc,μ⟩) ∧
      (arguments vals.length).map (·.val ⟨loc,μ⟩)=vals := by sorry
