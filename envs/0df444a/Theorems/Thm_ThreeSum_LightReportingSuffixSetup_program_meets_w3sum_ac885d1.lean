-- Prove2me | Theorems.Thm_ThreeSum_LightReportingSuffixSetup_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightReportingSuffixSetup.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:59:25.767551+00:00
-- url     : https://prove2.me/theorems/8f40bed0-19d6-4f55-b0dd-cbf6e8fc4d78
-- title:
--   Light Reporting Suffix Setup: program meets
-- statement:
--   The Light Reporting Suffix Setup construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixSetup.lean#L129-L179
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixSetup.lean#L129-L179

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixTable
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
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
open ThreeSum ThreeSum.LightReportingSuffixSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix
variable {lim : Limits}

theorem ThreeSum.LightReportingSuffixSetup.program_meets_w3sum_ac885d1 {μ : ℕ → ℤ} {W V offset sourceCut boxCut stage baseL baseR boxBase maskBase work B D d : ℕ}
    (hfit : offset+V ≤ W) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : sourceCut ≤ W) (hboxCut : boxCut ≤ V)
    (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W sourceCut ≤ boxBase)
    (hdataR : baseR+(W+1)*downsetCap W sourceCut ≤ boxBase)
    (hbox : boxBase+(V+1)*downsetCap V boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap V boxCut ≤ work)
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^V*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (hpreL : preL.card+boxCut ≤ sourceCut) (hpreR : preR.card+boxCut ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR sourceCut g W)
    (hd : d+W+11 ≤ lim.depth) :
    Meets lim program 29 d
      [W,sourceCut,boxCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
        V,offset,baseL,baseR,boxBase,maskBase,work] μ (time W V boxCut offset)
      (fun _ μ' =>
        LightBoxStages.StoredThrough μ' boxBase boxCut (leafWeight hfit f g stage preL preR) V ∧
        LightZetaStages.StoredThrough μ' baseL sourceCut f W ∧
        LightZetaStages.StoredThrough μ' baseR sourceCut g W ∧
        KeptBut μ μ' maskBase boxBase ((V+1)*downsetCap V boxCut)) := by sorry
