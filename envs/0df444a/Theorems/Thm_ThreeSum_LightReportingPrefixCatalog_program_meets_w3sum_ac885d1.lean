-- Prove2me | Theorems.Thm_ThreeSum_LightReportingPrefixCatalog_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightReportingPrefixCatalog.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:43:06.818803+00:00
-- url     : https://prove2.me/theorems/b1abf080-5c5b-4dba-bcc8-9d995ef4ff06
-- title:
--   Light Reporting Prefix Catalog: program meets
-- statement:
--   The Light Reporting Prefix Catalog construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPrefixCatalog.lean#L74-L179
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPrefixCatalog.lean#L74-L179

import Definitions.Def_Submission_ThreeSum_LightReportingPrefixArrays
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCatalogSetup
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
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
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_8a2cd73670b38080
import Definitions.Def_WeightedCache3SUM_Alias_f4a3749c14d0f5f9
import Theorems.Thm_ThreeSum_LightReportingSuffixBoxes_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_1d08961f6f3268cd
import Definitions.Def_WeightedCache3SUM_Alias_b15542bf609bcf98
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
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingPrefixCatalog
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPrefixCatalog ReportingHostPrefixOrder ReportingHostSuffix
open LightReportingSuffixCatalog
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits}

theorem ThreeSum.LightReportingPrefixCatalog.program_meets_w3sum_ac885d1 {μ : ℕ → ℤ}
    {h J k cut boxCut baseL baseR srcS pairL pairR stageL stageR ptrBase boxBase maskBase work B D d : ℕ}
    (hk : k ≤ J) (f g : Finset (Fin (J*(512*h))) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hcut : cut ≤ J*(512*h)) (hboxCut : boxCut ≤ (J-k)*(512*h))
    (hdataL : baseL+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ srcS)
    (hdataR : baseR+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ srcS)
    (hS : srcS+(512*h).choose h ≤ pairL)
    (hL : pairL+LightReportingPrefixArrays.localCount (512*h) h ≤ pairR)
    (hR : pairR+LightReportingPrefixArrays.localCount (512*h) h ≤ stageL)
    (hstageL : LightRadixKeys.space stageL (LightReportingPrefixArrays.localCount (512*h) h) k ≤ stageR)
    (hstageR : LightRadixKeys.space stageR (LightReportingPrefixArrays.localCount (512*h) h) k ≤ ptrBase)
    (hptr : ptrBase+count h k ≤ boxBase)
    (hbox : boxBase+count h k*stride ((J-k)*(512*h)) boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap ((J-k)*(512*h)) boxCut ≤ work)
    (hpairSpace : work+2*(512*h)+2 ≤ lim.space)
    (hspace : work+1+tableSize (J*(512*h))+(J*(512*h)+1) ≤ lim.space)
    (hpowWord : ((2^(512*h+1) : ℕ) : ℤ) ≤ lim.word)
    (hkeysWord : (LightRadixKeys.word (2^(512*h)) (2^(512*h)) k : ℤ) ≤ lim.word)
    (hword : (((J*(512*h)+1)*2^(J*(512*h)+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^((J-k)*(512*h))*
      ((2^((J-k)*(512*h))*B)*(2^((J-k)*(512*h))*D)) : ℕ) : ℤ) ≤ lim.word)
    (hpre : k*h+boxCut ≤ cut)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ B) (hg : ∀ S, S.card ≤ cut → |g S| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f (J*(512*h)))
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g (J*(512*h)))
    (hdPair : d+512*h+k+5 ≤ lim.depth) (hd : d+J*(512*h)+14 ≤ lim.depth) :
    Meets lim program 43 d
      [J*(512*h),cut,boxCut,(J-k)*(512*h),(J-k)*(512*h),k*(512*h),baseL,baseR,
        512*h,h,k,srcS,pairL,pairR,stageL,stageR,ptrBase,boxBase,maskBase,work]
      μ (time h J k boxCut)
      (fun r μ' =>
        r = (stageL+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k : ℕ) ∧
        SegN μ' ptrBase (List.ofFn fun i : Fin (count h k) =>
          boxBase+i.val*stride ((J-k)*(512*h)) boxCut) ∧
        (∀ i < count h k, LightBoxStages.StoredThrough μ'
          (boxBase+i*stride ((J-k)*(512*h)) boxCut) boxCut
          (leafWeight (block_fit hk) f g ((J-k)*(512*h)) (preL h J k i) (preR h J k i))
          ((J-k)*(512*h))) ∧
        LightZetaStages.StoredThrough μ' baseL cut f (J*(512*h)) ∧
        LightZetaStages.StoredThrough μ' baseR cut g (J*(512*h)) ∧
        μ' (stageL+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k) =
          (count h k : ℤ) ∧
        (∀ i < count h k,
          μ' (stageL+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k+1+i) =
            (subsetMask (preL h J k i) : ℤ)) ∧
        (∀ i < count h k,
          μ' (stageR+LightRadixKeys.offset (LightReportingPrefixArrays.localCount (512*h) h) k+1+i) =
            (subsetMask (preR h J k i) : ℤ)) ∧
        Kept μ μ' srcS) := by sorry
