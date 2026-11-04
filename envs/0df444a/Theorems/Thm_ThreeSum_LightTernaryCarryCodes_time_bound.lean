-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryCarryCodes_time_bound
-- name    : ThreeSum.LightTernaryCarryCodes.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:19:23.487067+00:00
-- url     : https://prove2.me/theorems/3dba3138-ab0a-4c79-b850-0c603c0d842e
-- title:
--   Light Ternary Carry Codes: time bound
-- statement:
--   The Light Ternary Carry Codes construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCarryCodes.lean#L283-L294
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCarryCodes.lean#L283-L294

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCarryCodes
open Light TernarySignedDigits
set_option maxHeartbeats 2400000
set_option maxRecDepth 9000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}

theorem ThreeSum.LightTernaryCarryCodes.time_bound (J : ℕ) : time J≤2000*2^J*(J+2)^2 := by sorry
