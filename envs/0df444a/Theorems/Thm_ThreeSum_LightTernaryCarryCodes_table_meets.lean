-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryCarryCodes_table_meets
-- name    : ThreeSum.LightTernaryCarryCodes.table_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:07:28.961085+00:00
-- url     : https://prove2.me/theorems/464bd940-0a7c-4e26-a513-3ccfe306c874
-- title:
--   Light Ternary Carry Codes: table meets
-- statement:
--   The Light Ternary Carry Codes construction uses the table meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCarryCodes.lean#L120-L197
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCarryCodes.lean#L120-L197

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

theorem ThreeSum.LightTernaryCarryCodes.table_meets {pTable pRow pDecode pDivide Q J dst work : ℕ}
    (htable : P[pTable]?=some (tableBody pRow))
    (hrow : P[pRow]?=some (rowBody pDecode))
    (hdecode : P[pDecode]?=some (LightOutputDecodeDigits.body pDivide))
    (hdivide : P[pDivide]?=some LightOutputDecodeDivide.body)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+3<lim.depth)
    (hsep : dst+Q*(J+1)≤work)
    (hspace : space work Q≤lim.space)
    (hword : (word J Q : ℤ)≤lim.word) :
    Meets lim P pTable d [Q,J,dst,work] μ (tableTime Q J)
      (fun r ν => r=(Q : ℤ) ∧ Table ν dst J Q ∧ Kept μ ν dst) := by sorry
