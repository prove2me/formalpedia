-- Prove2me | Theorems.Thm_ThreeSum_LightOutputDecodeDigits_meets_w3sum_ac885d1
-- name    : ThreeSum.LightOutputDecodeDigits.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:22:52.68095+00:00
-- url     : https://prove2.me/theorems/af132160-3e03-40d2-834e-6bc8674cb8ed
-- title:
--   Light Output Decode Digits: meets
-- statement:
--   The Light Output Decode Digits construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOutputDecodeDigits.lean#L42-L142
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOutputDecodeDigits.lean#L42-L142

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDivide
import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52

set_option autoImplicit false
open ThreeSum ThreeSum.LightOutputDecodeDigits
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {k J m dst work V : ℕ}

theorem ThreeSum.LightOutputDecodeDigits.meets_w3sum_ac885d1 {pMain pDivide : ℕ}
    (hmain : P[pMain]?=some (body pDivide))
    (hdivide : P[pDivide]?=some LightOutputDecodeDivide.body)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hm : 1 ≤ m) (hk : k ≤ V) (hsep : dst+J ≤ work)
    (hspace : space work V ≤ lim.space)
    (hword : (word V m J : ℤ) ≤ lim.word) :
    Meets lim P pMain d [k,J,m,dst,work] μ (time J V)
      (fun r ν => r=((k/m^J : ℕ) : ℤ) ∧
        (∀ j < J, ν (dst+j)=((OutputDecodeOrder.indices m J k).getD j 0 : ℤ)) ∧
        Kept μ ν dst) := by sorry
