-- Prove2me | Theorems.Thm_ThreeSum_LightExplicitSum_program_meets
-- name    : ThreeSum.LightExplicitSum.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:12:48.61596+00:00
-- url     : https://prove2.me/theorems/cf30059c-2089-4dfd-82f3-0ab9ada88fcf
-- title:
--   Light Explicit Sum: program meets
-- statement:
--   The Light Explicit Sum construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExplicitSum.lean#L243-L266
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExplicitSum.lean#L243-L266

import Definitions.Def_Submission_ThreeSum_ExplicitLayers
import Definitions.Def_Submission_ThreeSum_LightLeafSum
import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Definitions.Def_Submission_ThreeSum_LightExplicitSum
import Theorems.Thm_ThreeSum_LightBoxStages_program_meets
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_meets
import Theorems.Thm_ThreeSum_LightDownsetSize_program_meets
import Theorems.Thm_ThreeSum_LightLeafSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightQueryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightQueryWeights_program_meets
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
open ThreeSum ThreeSum.LightExplicitSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open QueryCoordinates
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightExplicitSum.program_meets    {μ : ℕ → ℤ} {W cut stage t maskBase baseL baseR work B D d : ℕ}
    (Q preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ maskBase)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ maskBase)
    (hmasks : maskBase+layerOffset Q.card t ≤ work)
    (hspace : work+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : (((layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1)
    (hdisjL : Disjoint preL Q) (hdisjR : Disjoint preR Q)
    (hcardL : (preL ∪ Q).card ≤ cut) (hcardR : (preR ∪ Q).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hd : d+W+8 ≤ lim.depth) :
    Meets lim program 0 d
      [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,Q.card,subsetMask Q,
        t,baseL,baseR,maskBase,work] μ (time W Q.card t)
      (fun r μ' => r = ExplicitLayers.valueSum Q (SignedLeaf.value f g stage preL preR) t ∧
        KeptBut μ μ' work maskBase (layerOffset Q.card t)) := by sorry
