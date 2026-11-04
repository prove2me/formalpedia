-- Prove2me | Theorems.Thm_ThreeSum_LightSourceOccurrenceArray_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSourceOccurrenceArray.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:33:14.112664+00:00
-- url     : https://prove2.me/theorems/f4bfe84b-254a-4a32-97fa-d9c94d112050
-- title:
--   Light Source Occurrence Array: meets
-- statement:
--   The Light Source Occurrence Array construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceOccurrenceArray.lean#L33-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceOccurrenceArray.lean#L33-L82

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_LightSourceOccurrenceArray
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceOccurrenceArray
open Light OutputDecodeOrder
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceOccurrenceArray.meets_w3sum_ac885d1 {pMain pDigits pDivide : ℕ}
    (hmain : P[pMain]?=some (body pDigits))
    (hdigits : P[pDigits]?=some (LightOutputDecodeDigits.body pDivide))
    (hdivide : P[pDivide]?=some LightOutputDecodeDivide.body)
    {μ : ℕ → ℤ} {N J m dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hm : 1 ≤ m)
    (hsep : dst+N*J ≤ work) (hspace : LightOutputDecodeDigits.space work N ≤ lim.space)
    (hword : (LightOutputDecodeDigits.word N m J : ℤ) ≤ lim.word) :
    Meets lim P pMain d [N,J,m,dst,work] μ (time N J) (fun _ ν =>
      (∀ i < N, ∀ j < J, ν (dst+i*J+j)=((indices m J i).getD j 0 : ℤ)) ∧ Kept μ ν dst) := by sorry
