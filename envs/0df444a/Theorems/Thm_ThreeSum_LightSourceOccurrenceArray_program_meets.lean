-- Prove2me | Theorems.Thm_ThreeSum_LightSourceOccurrenceArray_program_meets
-- name    : ThreeSum.LightSourceOccurrenceArray.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:37:17.142194+00:00
-- url     : https://prove2.me/theorems/a58bf066-b9d1-4a23-a414-4c0335dcd362
-- title:
--   Light Source Occurrence Array: program meets
-- statement:
--   The Light Source Occurrence Array construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceOccurrenceArray.lean#L86-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceOccurrenceArray.lean#L86-L92

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_LightSourceOccurrenceArray
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDigits_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceOccurrenceArray
open Light OutputDecodeOrder
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceOccurrenceArray.program_meets {μ : ℕ → ℤ} {N J m dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hm : 1 ≤ m)
    (hsep : dst+N*J ≤ work) (hspace : LightOutputDecodeDigits.space work N ≤ lim.space)
    (hword : (LightOutputDecodeDigits.word N m J : ℤ) ≤ lim.word) :
    Meets lim program 0 d [N,J,m,dst,work] μ (time N J) (fun _ ν =>
      (∀ i < N, ∀ j < J, ν (dst+i*J+j)=((indices m J i).getD j 0 : ℤ)) ∧ Kept μ ν dst) := by sorry
