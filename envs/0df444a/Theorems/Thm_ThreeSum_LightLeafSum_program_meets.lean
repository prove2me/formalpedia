-- Prove2me | Theorems.Thm_ThreeSum_LightLeafSum_program_meets
-- name    : ThreeSum.LightLeafSum.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:05:16.731478+00:00
-- url     : https://prove2.me/theorems/2b315cab-fcde-44bd-8fec-0cc9f7b24d8f
-- title:
--   Light Leaf Sum: program meets
-- statement:
--   The Light Leaf Sum construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLeafSum.lean#L190-L216
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLeafSum.lean#L190-L216

import Definitions.Def_Submission_ThreeSum_LightSignedLeaf
import Definitions.Def_Submission_ThreeSum_LightLeafSum
import Theorems.Thm_ThreeSum_LightBoxStages_program_meets
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_meets
import Theorems.Thm_ThreeSum_LightDownsetSize_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightSign_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_program_meets
import Theorems.Thm_ThreeSum_LightStageLookup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightZetaCell_program_meets
import Theorems.Thm_ThreeSum_LightZetaPass_program_meets
import Theorems.Thm_ThreeSum_LightZetaStages_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightLeafSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightLeafSum.program_meets {μ : ℕ → ℤ} {W cut stage t maskBase baseL baseR work B D d : ℕ}
    (Q preL preR : Finset (Fin W)) (missing : List (Finset (Fin W)))
    (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ work)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ work)
    (hmasks : maskBase+missing.length ≤ work)
    (hspace : work+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : ((missing.length*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (hdisjL : Disjoint preL Q) (hdisjR : Disjoint preR Q)
    (hcardL : (preL ∪ Q).card ≤ cut) (hcardR : (preR ∪ Q).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hvalid : ∀ U ∈ missing, U ⊆ Q ∧ U.card = t)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hseg : SegN μ maskBase (missing.map subsetMask))
    (hd : d+W+7 ≤ lim.depth) :
    Meets lim program 0 d
      [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,Q.card,subsetMask Q,
        t,missing.length,maskBase,baseL,baseR,work] μ (time W missing.length)
      (fun r μ' => r = (missing.map (term Q preL preR f g stage)).sum ∧ Kept μ μ' work) := by sorry
