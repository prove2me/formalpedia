-- Prove2me | Theorems.Thm_ThreeSum_LightScales_program_meets
-- name    : ThreeSum.LightScales.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:19:15.752375+00:00
-- url     : https://prove2.me/theorems/2ce44a2f-3066-467e-b0d5-a41139772bcd
-- title:
--   Light Scales: program meets
-- statement:
--   The Light Scales construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightScales.lean#L161-L166
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightScales.lean#L161-L166

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightScales
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightScales
open Light ThreeSum.Scales
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightScales.program_meets {μ : ℕ → ℤ} {n dst d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : dst+5 ≤ lim.space)
    (hword : ((1000*(n+1) : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim program 0 d [n,dst] μ (time n)
      (fun r μ' => r = (mu n : ℤ) ∧ Seg μ' dst (values n) ∧ SameOutside μ μ' dst 5) := by sorry
