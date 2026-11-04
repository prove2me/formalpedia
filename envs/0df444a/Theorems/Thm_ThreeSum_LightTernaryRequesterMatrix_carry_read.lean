-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryRequesterMatrix_carry_read
-- name    : ThreeSum.LightTernaryRequesterMatrix.carry_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:08:08.281494+00:00
-- url     : https://prove2.me/theorems/52e30fdf-eef3-4b67-a45f-533e75d77882
-- title:
--   Light Ternary Requester Matrix: carry read
-- statement:
--   The Light Ternary Requester Matrix construction uses the carry read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRequesterMatrix.lean#L44-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRequesterMatrix.lean#L44-L56

import Definitions.Def_Submission_ThreeSum_LightTernaryOriginalRequester
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_LightTernaryRequesterMatrix
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRequesterMatrix
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightTernaryRequesterMatrix.carry_read {μ : ℕ → ℤ} {carry J Q q : ℕ}
    (H : LightTernaryCarryCodes.Table μ carry J Q) (hq : q<Q) :
    ∀k≤J, μ (carry+q*(J+1)+k)=carryAt (TernaryCarryCode.carryFromCode J q) (J-k) := by sorry
