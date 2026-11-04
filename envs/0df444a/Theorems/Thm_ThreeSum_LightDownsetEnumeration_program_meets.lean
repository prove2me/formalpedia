-- Prove2me | Theorems.Thm_ThreeSum_LightDownsetEnumeration_program_meets
-- name    : ThreeSum.LightDownsetEnumeration.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:47:16.166705+00:00
-- url     : https://prove2.me/theorems/287903fa-1c4d-4c72-94a7-3037a931ad76
-- title:
--   Light Downset Enumeration: program meets
-- statement:
--   The Light Downset Enumeration construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetEnumeration.lean#L164-L174
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetEnumeration.lean#L164-L174

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightDownsetEnumeration
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightDownsetEnumeration.program_meets {L cut dst powers d : ℕ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hcut : cut ≤ L) (hdst : dst+downsetCap L cut ≤ powers)
    (hpowers : Powers μ powers L) (hd : d+L+1 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,dst,powers] μ (time L cut)
      (fun r μ' => r = (downsetCap L cut : ℤ) ∧
        SegN μ' dst (enumerateDownset L cut) ∧
        SameOutside μ μ' dst (downsetCap L cut)) := by sorry
