-- Prove2me | Theorems.Thm_ThreeSum_LightDownsetEnumerationSetup_program_meets
-- name    : ThreeSum.LightDownsetEnumerationSetup.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:19:14.750132+00:00
-- url     : https://prove2.me/theorems/7e0e88c4-bb06-4aa9-a51d-2c2330edfdac
-- title:
--   Light Downset Enumeration Setup: program meets
-- statement:
--   The Light Downset Enumeration Setup construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetEnumerationSetup.lean#L68-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetEnumerationSetup.lean#L68-L78

import Definitions.Def_Submission_ThreeSum_LightDownsetEnumeration
import Definitions.Def_Submission_ThreeSum_LightDownsetEnumerationSetup
import Theorems.Thm_ThreeSum_LightDownsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetEnumerationSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightDownsetEnumerationSetup.program_meets {μ : ℕ → ℤ} {L cut dst work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hcut : cut ≤ L) (hdst : dst+downsetCap L cut ≤ work)
    (hd : d+L+2 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,dst,work] μ (time L cut)
      (fun r μ' => r = (downsetCap L cut : ℤ) ∧
        SegN μ' dst (enumerateDownset L cut) ∧ Powers μ' work L ∧
        KeptBut μ μ' work dst (downsetCap L cut)) := by sorry
