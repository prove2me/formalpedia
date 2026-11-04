-- Prove2me | Theorems.Thm_ThreeSum_LightWeightDecode_program_meets
-- name    : ThreeSum.LightWeightDecode.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:49:15.531656+00:00
-- url     : https://prove2.me/theorems/7249e865-6525-49d5-83ee-546b48473ab5
-- title:
--   Light Weight Decode: program meets
-- statement:
--   The Light Weight Decode construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightDecode.lean#L115-L124
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightDecode.lean#L115-L124

import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightWeightDecode
import Theorems.Thm_ThreeSum_LightRadixDigit_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
import Theorems.Thm_ThreeSum_LightWeightRow_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightDecode
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightWeightDecode.program_meets
    {μ : ℕ → ℤ} {L p k dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hp : 1 ≤ p)
    (hdst : dst+2*L ≤ work) (hspace : work+(2*L+1) ≤ lim.space)
    (hword : (word L p k : ℤ) ≤ lim.word) :
    Meets lim program 0 d [L,p,k,dst,work] μ (time L k)
      (fun _ μ' => Rows μ' dst L p k ∧
        (∀ e ≤ 2*L, μ' (work+e) = ((p^e : ℕ) : ℤ)) ∧
        KeptBut μ μ' work dst (2*L)) := by sorry
