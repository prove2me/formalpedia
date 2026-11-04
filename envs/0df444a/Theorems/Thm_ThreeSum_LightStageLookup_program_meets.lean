-- Prove2me | Theorems.Thm_ThreeSum_LightStageLookup_program_meets
-- name    : ThreeSum.LightStageLookup.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:48:15.857518+00:00
-- url     : https://prove2.me/theorems/08c43dd3-7dac-4733-960c-638e0d2fcdc5
-- title:
--   Light Stage Lookup: program meets
-- statement:
--   The Light Stage Lookup construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightStageLookup.lean#L83-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightStageLookup.lean#L83-L93

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBoxStages
import Definitions.Def_Submission_ThreeSum_LightDownsetAddress
import Definitions.Def_Submission_ThreeSum_LightStageLookup
import Theorems.Thm_ThreeSum_LightBoxStages_program_meets
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_meets
import Theorems.Thm_ThreeSum_LightDownsetSize_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets
import Theorems.Thm_ThreeSum_LightZetaCell_program_meets
import Theorems.Thm_ThreeSum_LightZetaPass_program_meets
import Theorems.Thm_ThreeSum_LightZetaStages_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightStageLookup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightStageLookup.program_meets {μ : ℕ → ℤ} {L cut base j work d : ℕ}
    (S : Finset (Fin L)) (value : ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hS : S.card ≤ cut) (hj : j ≤ L)
    (hread : μ (readAddr cut base j S) = value) (hd : d+L+5 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,S.card,subsetMask S,j,base,work] μ (time L)
      (fun r μ' => r = value ∧ Kept μ μ' work) := by sorry
