-- Prove2me | Theorems.Thm_ThreeSum_LightSwitch_test_holds_iff
-- name    : ThreeSum.LightSwitch.test_holds_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:35:51.013349+00:00
-- url     : https://prove2.me/theorems/dc8b6e0f-00fd-4814-96d2-7d4af2796ad5
-- title:
--   Light Switch: test holds iff
-- statement:
--   The Light Switch construction uses the test holds iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitch.lean#L56-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSwitch.lean#L56-L63

import Definitions.Def_Submission_ThreeSum_LightSwitchBounds
import Definitions.Def_Submission_ThreeSum_LightSwitchScalar
import Definitions.Def_Submission_ThreeSum_LightSwitch
set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitch
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {μ : ℕ→ℤ} {J j r q d : ℕ}

theorem ThreeSum.LightSwitch.test_holds_iff (hj : j ≤ J) :
    test.Holds ⟨frame [(J : ℤ),j,r,q],μ⟩ ↔ factor J j*cubic r q < left J j r := by sorry
