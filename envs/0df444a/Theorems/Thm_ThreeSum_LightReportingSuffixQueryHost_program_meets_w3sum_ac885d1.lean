-- Prove2me | Theorems.Thm_ThreeSum_LightReportingSuffixQueryHost_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightReportingSuffixQueryHost.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:27:57.323114+00:00
-- url     : https://prove2.me/theorems/db0b1b84-abe8-482a-b79a-773222272cd2
-- title:
--   Light Reporting Suffix Query Host: program meets
-- statement:
--   The Light Reporting Suffix Query Host construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixQueryHost.lean#L28-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixQueryHost.lean#L28-L89

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixQuery
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixLower
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixQueryHost
import Theorems.Thm_ThreeSum_LightBlockBoxes_program_meets
import Theorems.Thm_ThreeSum_LightBlockQuery_program_meets
import Theorems.Thm_ThreeSum_LightBoxStages_program_meets
import Theorems.Thm_ThreeSum_LightBoxSum_program_meets
import Theorems.Thm_ThreeSum_LightCanonicalBoxSum_program_meets
import Theorems.Thm_ThreeSum_LightDownsetAddress_program_meets
import Theorems.Thm_ThreeSum_LightDownsetSize_program_meets
import Theorems.Thm_ThreeSum_LightExplicitSum_program_meets
import Theorems.Thm_ThreeSum_LightLeafSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskMinimum_program_meets
import Theorems.Thm_ThreeSum_LightMaskUnion_program_meets
import Theorems.Thm_ThreeSum_LightQueryBox_program_meets
import Theorems.Thm_ThreeSum_LightQueryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightQueryWeights_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_dfc7d85d435022ae
import Theorems.Thm_ThreeSum_LightSign_program_meets
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafGeneral_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafTable_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_program_meets
import Theorems.Thm_ThreeSum_LightSparseQuery_program_meets
import Theorems.Thm_ThreeSum_LightStageLookup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightZetaCell_program_meets
import Theorems.Thm_ThreeSum_LightZetaPass_program_meets
import Theorems.Thm_ThreeSum_LightZetaStages_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixQueryHost
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix
variable {lim : Limits}

theorem ThreeSum.LightReportingSuffixQueryHost.program_meets_w3sum_ac885d1
    {μ : ℕ → ℤ} {W V offset cut stage t baseL baseR boxCut boxBase maskBase work B D d : ℕ}
    (hfit : offset+V ≤ W) (Q : Finset (Fin V)) (preL preR : Finset (Fin W))
    (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ maskBase)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ maskBase)
    (hdataBox : boxBase+(V+1)*downsetCap V boxCut ≤ maskBase)
    (hmasks : maskBase+LightSparseQuery.queryItems Q.card t ≤ work)
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : (LightSparseQuery.magnitudeBound V stage Q.card t B D : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1) (hboxCut : boxCut ≤ Q.card) (hflags : Q.card-t ≤ boxCut)
    (hdisjL : Disjoint preL (liftSet hfit Q)) (hdisjR : Disjoint preR (liftSet hfit Q))
    (hcardL : (preL ∪ liftSet hfit Q).card ≤ cut)
    (hcardR : (preR ∪ liftSet hfit Q).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hstoredBox : LightBoxStages.StoredThrough μ boxBase boxCut (leafWeight hfit f g stage preL preR) V)
    (hd : d+W+10 ≤ lim.depth) :
    Meets lim program 30 d
      [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,V,offset,
        Q.card,subsetMask (liftSet hfit Q),t,baseL,baseR,boxCut,boxBase,maskBase,work]
      μ (time W V Q.card t)
      (fun r μ' =>
        r = Subset.mobius (fun S => SubsetStages.stageValue f stage (preL ∪ S)*
          SubsetStages.stageValue g stage (preR ∪ S)) (liftSet hfit Q) ∧
        KeptBut μ μ' work maskBase (LightSparseQuery.queryItems Q.card t)) := by sorry
