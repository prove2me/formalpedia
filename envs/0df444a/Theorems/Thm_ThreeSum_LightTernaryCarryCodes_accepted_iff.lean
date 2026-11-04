-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryCarryCodes_accepted_iff
-- name    : ThreeSum.LightTernaryCarryCodes.accepted_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:07:46.704998+00:00
-- url     : https://prove2.me/theorems/ba44f936-3f13-499e-aaf6-3a8d800c51f2
-- title:
--   Light Ternary Carry Codes: accepted iff
-- statement:
--   The Light Ternary Carry Codes construction uses the accepted iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCarryCodes.lean#L102-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCarryCodes.lean#L102-L104

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

theorem ThreeSum.LightTernaryCarryCodes.accepted_iff {J q : ℕ} (hq : q<2^J) :
    accepted J q=1 ↔ digit 2 q 0=0 := by sorry
