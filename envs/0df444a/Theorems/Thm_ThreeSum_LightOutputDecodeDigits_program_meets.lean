-- Prove2me | Theorems.Thm_ThreeSum_LightOutputDecodeDigits_program_meets
-- name    : ThreeSum.LightOutputDecodeDigits.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:28:16.309328+00:00
-- url     : https://prove2.me/theorems/179e4c15-c6e1-4fea-ad12-b7a50391b9af
-- title:
--   Light Output Decode Digits: program meets
-- statement:
--   The Light Output Decode Digits construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOutputDecodeDigits.lean#L146-L154
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOutputDecodeDigits.lean#L146-L154

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDivide
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightOutputDecodeDigits
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {k J m dst work V : ℕ}

theorem ThreeSum.LightOutputDecodeDigits.program_meets
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hm : 1 ≤ m) (hk : k ≤ V) (hsep : dst+J ≤ work)
    (hspace : space work V ≤ lim.space)
    (hword : (word V m J : ℤ) ≤ lim.word) :
    Meets lim program 0 d [k,J,m,dst,work] μ (time J V)
      (fun r ν => r=((k/m^J : ℕ) : ℤ) ∧
        (∀ j < J, ν (dst+j)=((OutputDecodeOrder.indices m J k).getD j 0 : ℤ)) ∧
        Kept μ ν dst) := by sorry
