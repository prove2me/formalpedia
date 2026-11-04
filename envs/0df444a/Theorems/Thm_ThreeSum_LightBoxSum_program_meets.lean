-- Prove2me | Theorems.Thm_ThreeSum_LightBoxSum_program_meets
-- name    : ThreeSum.LightBoxSum.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:06:31.417558+00:00
-- url     : https://prove2.me/theorems/40c00bd2-8770-45c1-b20f-bbf7e2b6d2f7
-- title:
--   Light Box Sum: program meets
-- statement:
--   The Light Box Sum construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBoxSum.lean#L161-L177
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBoxSum.lean#L161-L177

import Definitions.Def_Submission_ThreeSum_LightQueryBox
import Definitions.Def_Submission_ThreeSum_BoxBounds
import Definitions.Def_Submission_ThreeSum_LightBoxSum
import Theorems.Thm_ThreeSum_LightBoxStages_program_meets
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_meets
import Theorems.Thm_ThreeSum_LightDownsetSize_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskMinimum_program_meets
import Theorems.Thm_ThreeSum_LightQueryBox_program_meets
import Theorems.Thm_ThreeSum_LightStageLookup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets
import Theorems.Thm_ThreeSum_LightZetaCell_program_meets
import Theorems.Thm_ThreeSum_LightZetaPass_program_meets
import Theorems.Thm_ThreeSum_LightZetaStages_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightBoxSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightBoxSum.program_meets {μ : ℕ → ℤ} {L cut t maskBase base work B d : ℕ}
    (Q : Finset (Fin L)) (missing : List (Finset (Fin L))) (weight : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*downsetCap L cut ≤ work) (hmasks : maskBase+missing.length ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : ((missing.length*(2^L*B) : ℕ) : ℤ) ≤ lim.word)
    (hvalid : ∀ U ∈ missing, U ⊆ Q ∧ U.card = t ∧ (Q \ U).card ≤ cut)
    (hweight : ∀ S, S.card ≤ cut → |weight S| ≤ B)
    (hstored : LightBoxStages.StoredThrough μ base cut weight L)
    (hseg : SegN μ maskBase (missing.map subsetMask))
    (hd : d+L+7 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,Q.card,subsetMask Q,t,missing.length,maskBase,base,work]
      μ (time L missing.length)
      (fun r μ' => r = (missing.map (boxValue Q weight)).sum ∧ Kept μ μ' work) := by sorry
