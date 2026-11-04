-- Prove2me | Theorems.Thm_ThreeSum_LightDownsetAddress_program_meets
-- name    : ThreeSum.LightDownsetAddress.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:47:04.934533+00:00
-- url     : https://prove2.me/theorems/99fab34d-0260-491f-9136-506ea7e66fea
-- title:
--   Light Downset Address: program meets
-- statement:
--   The Light Downset Address construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetAddress.lean#L80-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetAddress.lean#L80-L87

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Definitions.Def_Submission_ThreeSum_LightDownsetAddress
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetAddress
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightDownsetAddress.program_meets {μ : ℕ → ℤ} {L k m work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hm : IsMask L k m) (hd : d+L+4 ≤ lim.depth) :
    Meets lim program 0 d [L,k,m,work] μ (time L)
      (fun r μ' => r = (downsetRank L m : ℤ) ∧ Kept μ μ' work) := by sorry
