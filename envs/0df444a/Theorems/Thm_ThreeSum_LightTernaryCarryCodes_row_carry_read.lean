-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryCarryCodes_row_carry_read
-- name    : ThreeSum.LightTernaryCarryCodes.row_carry_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:07:25.92795+00:00
-- url     : https://prove2.me/theorems/e2b3f96b-b35b-41ca-b1b8-039c835abb1d
-- title:
--   Light Ternary Carry Codes: row carry read
-- statement:
--   The Light Ternary Carry Codes construction uses the row carry read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCarryCodes.lean#L255-L262
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCarryCodes.lean#L255-L262

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

theorem ThreeSum.LightTernaryCarryCodes.row_carry_read {ν : ℕ → ℤ} {dst J q : ℕ}
    (h : Row ν dst J q) (i : Fin (J+1)) :
    ν (dst+J-i.val)=((TernaryCarryCode.carryFromCode J q i).val : ℤ) := by sorry
