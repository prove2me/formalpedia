-- Prove2me | Theorems.Thm_ThreeSum_LightReportingSuffixCatalog_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightReportingSuffixCatalog.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:32:45.551331+00:00
-- url     : https://prove2.me/theorems/4527d57d-41a9-42a1-8665-56a318b6f057
-- title:
--   Light Reporting Suffix Catalog: program meets
-- statement:
--   The Light Reporting Suffix Catalog construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixCatalog.lean#L49-L166
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixCatalog.lean#L49-L166

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostQueryBounds
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCatalog
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
import Definitions.Def_WeightedCache3SUM_Alias_c19df7a51d8d0351
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
open ThreeSum ThreeSum.LightReportingSuffixCatalog
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix ReportingHostQueryBounds
set_option maxHeartbeats 1800000
variable {lim : Limits}

theorem ThreeSum.LightReportingSuffixCatalog.program_meets_w3sum_ac885d1
    {μ : ℕ → ℤ} {W V offset cut boxCut stage cL cR baseL baseR inL inR n ptrBase boxBase maskBase work B D d : ℕ}
    (hfit : offset+V ≤ W) (preL preR : ℕ → Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hboxCut : boxCut ≤ V) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ ptrBase)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ ptrBase)
    (hinL : inL+n ≤ ptrBase) (hinR : inR+n ≤ ptrBase)
    (hptr : ptrBase+n ≤ boxBase) (hbox : boxBase+n*stride V boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap V boxCut ≤ work)
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^V*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (hcardL : ∀ i < n, (preL i).card = cL) (hcardR : ∀ i < n, (preR i).card = cR)
    (hpreL : cL+boxCut ≤ cut) (hpreR : cR+boxCut ≤ cut)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ B) (hg : ∀ S, S.card ≤ cut → |g S| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hreadL : ∀ i < n, μ (inL+i) = (subsetMask (preL i) : ℤ))
    (hreadR : ∀ i < n, μ (inR+i) = (subsetMask (preR i) : ℤ))
    (hd : d+W+12 ≤ lim.depth) :
    Meets lim program 30 d
      [W,cut,boxCut,stage,cL,cR,V,offset,baseL,baseR,inL,inR,n,
        ptrBase,boxBase,stride V boxCut,maskBase,work]
      μ (time W V boxCut offset n)
      (fun _ μ' =>
        SegN μ' ptrBase (List.ofFn fun i : Fin n => boxBase+i.val*stride V boxCut) ∧
        (∀ i < n, LightBoxStages.StoredThrough μ' (boxBase+i*stride V boxCut) boxCut
          (leafWeight hfit f g stage (preL i) (preR i)) V) ∧
        LightZetaStages.StoredThrough μ' baseL cut f W ∧
        LightZetaStages.StoredThrough μ' baseR cut g W ∧
        Kept μ μ' ptrBase) := by sorry
