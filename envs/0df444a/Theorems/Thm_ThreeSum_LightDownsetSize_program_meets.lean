-- Prove2me | Theorems.Thm_ThreeSum_LightDownsetSize_program_meets
-- name    : ThreeSum.LightDownsetSize.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:47:05.850552+00:00
-- url     : https://prove2.me/theorems/4ccaab2b-e1f3-47a0-826f-eaceba612226
-- title:
--   Light Downset Size: program meets
-- statement:
--   The Light Downset Size construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetSize.lean#L91-L98
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetSize.lean#L91-L98

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetSize
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightDownsetSize.program_meets {μ : ℕ → ℤ} {L cut work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hcut : cut ≤ L) (hd : d+L+4 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,work] μ (time L)
      (fun r μ' => r = (downsetCap L cut : ℤ) ∧ Kept μ μ' work) := by sorry
