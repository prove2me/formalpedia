-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryCarryCodes_program_meets
-- name    : ThreeSum.LightTernaryCarryCodes.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:37:35.248655+00:00
-- url     : https://prove2.me/theorems/0686169c-0ea5-457a-b860-1b7005aef3cb
-- title:
--   Light Ternary Carry Codes: program meets
-- statement:
--   The Light Ternary Carry Codes construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCarryCodes.lean#L246-L253
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCarryCodes.lean#L246-L253

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightNatPower_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDigits_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCarryCodes
open Light TernarySignedDigits
set_option maxHeartbeats 2400000
set_option maxRecDepth 9000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}

theorem ThreeSum.LightTernaryCarryCodes.program_meets {J dst work : ℕ}
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+4<lim.depth)
    (hsep : dst+2^J*(J+1)≤work)
    (hspace : space work (2^J)≤lim.space)
    (hword : (word J (2^J) : ℤ)≤lim.word) :
    Meets lim program 0 d [J,dst,work] μ (time J)
      (fun r ν => r=(2^J : ℕ) ∧ Table ν dst J (2^J) ∧ Kept μ ν dst) := by sorry
