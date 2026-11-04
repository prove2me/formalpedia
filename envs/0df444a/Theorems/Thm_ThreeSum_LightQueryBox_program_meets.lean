-- Prove2me | Theorems.Thm_ThreeSum_LightQueryBox_program_meets
-- name    : ThreeSum.LightQueryBox.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:57:42.700834+00:00
-- url     : https://prove2.me/theorems/fa3eaea0-497d-4255-82ef-ed3ff82ba34c
-- title:
--   Light Query Box: program meets
-- statement:
--   The Light Query Box construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightQueryBox.lean#L137-L150
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightQueryBox.lean#L137-L150

import Definitions.Def_Submission_ThreeSum_LightStageLookup
import Definitions.Def_Submission_ThreeSum_LightMaskMinimum
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_LightQueryBox
import Theorems.Thm_ThreeSum_LightBoxStages_program_meets
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_meets
import Theorems.Thm_ThreeSum_LightDownsetSize_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskMinimum_program_meets
import Theorems.Thm_ThreeSum_LightStageLookup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets
import Theorems.Thm_ThreeSum_LightZetaCell_program_meets
import Theorems.Thm_ThreeSum_LightZetaPass_program_meets
import Theorems.Thm_ThreeSum_LightZetaStages_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightQueryBox
open Light ThreeSum.SubsetAddress ThreeSum.MaskDifference
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightQueryBox.program_meets {μ : ℕ → ℤ} {L cut base work d : ℕ}
    (Q U : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hU : U ⊆ Q) (hflags : (Q \ U).card ≤ cut)
    (hstored : LightBoxStages.StoredThrough μ base cut weight L)
    (hd : d+L+6 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,Q.card,subsetMask Q,U.card,subsetMask U,base,work] μ (time L)
      (fun r μ' => r = SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight ∧
        Kept μ μ' work) := by sorry
