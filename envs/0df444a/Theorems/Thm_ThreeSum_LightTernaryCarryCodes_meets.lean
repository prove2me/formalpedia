-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryCarryCodes_meets
-- name    : ThreeSum.LightTernaryCarryCodes.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:33:21.458516+00:00
-- url     : https://prove2.me/theorems/292ed38a-f3c7-444e-be12-0303fa5c02f8
-- title:
--   Light Ternary Carry Codes: meets
-- statement:
--   The Light Ternary Carry Codes construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCarryCodes.lean#L207-L240
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCarryCodes.lean#L207-L240

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d92129e9a4741fac
import Definitions.Def_WeightedCache3SUM_Alias_54f2bf19dfb01d66
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCarryCodes
open Light TernarySignedDigits
set_option maxHeartbeats 2400000
set_option maxRecDepth 9000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}

theorem ThreeSum.LightTernaryCarryCodes.meets {pMain pPower pTable pRow pDecode pDivide J dst work : ℕ}
    (hmain : P[pMain]?=some (body pPower pTable))
    (hpower : P[pPower]?=some LightNatPower.body)
    (htable : P[pTable]?=some (tableBody pRow))
    (hrow : P[pRow]?=some (rowBody pDecode))
    (hdecode : P[pDecode]?=some (LightOutputDecodeDigits.body pDivide))
    (hdivide : P[pDivide]?=some LightOutputDecodeDivide.body)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+4<lim.depth)
    (hsep : dst+2^J*(J+1)≤work)
    (hspace : space work (2^J)≤lim.space)
    (hword : (word J (2^J) : ℤ)≤lim.word) :
    Meets lim P pMain d [J,dst,work] μ (time J)
      (fun r ν => r=(2^J : ℕ) ∧ Table ν dst J (2^J) ∧ Kept μ ν dst) := by sorry
