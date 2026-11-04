-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryCarryCodes_space_bound
-- name    : ThreeSum.LightTernaryCarryCodes.space_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:00:46.507135+00:00
-- url     : https://prove2.me/theorems/1cc4b291-98be-48b3-9a48-6a222c086e4c
-- title:
--   Light Ternary Carry Codes: space bound
-- statement:
--   The Light Ternary Carry Codes construction uses the space bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCarryCodes.lean#L296-L299
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCarryCodes.lean#L296-L299

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCarryCodes
open Light TernarySignedDigits
set_option maxHeartbeats 2400000
set_option maxRecDepth 9000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}

theorem ThreeSum.LightTernaryCarryCodes.space_bound (work J : ℕ) : space work (2^J)≤work+J+3 := by sorry
