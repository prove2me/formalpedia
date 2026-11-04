-- Prove2me | Theorems.Thm_ThreeSum_LightReportingCatalogQuery_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightReportingCatalogQuery.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:38:32.065037+00:00
-- url     : https://prove2.me/theorems/1a4d7028-607f-4f60-9eaf-704e57d8faf4
-- title:
--   Light Reporting Catalog Query: program meets
-- statement:
--   The Light Reporting Catalog Query construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingCatalogQuery.lean#L41-L129
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingCatalogQuery.lean#L41-L129

import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogSelection
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogQuery
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
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
import Definitions.Def_WeightedCache3SUM_Alias_bb907f0b533f0452
import Definitions.Def_WeightedCache3SUM_Alias_7f1c96094f5b1c13
import Theorems.Thm_ThreeSum_LightReportingPackKeys_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_8a2cd73670b38080
import Definitions.Def_WeightedCache3SUM_Alias_f4a3749c14d0f5f9
import Definitions.Def_WeightedCache3SUM_Alias_a2387e9e7b890e99
import Definitions.Def_WeightedCache3SUM_Alias_a02564c7d1f1443e
import Theorems.Thm_ThreeSum_LightReportingSuffixBoxes_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_1d08961f6f3268cd
import Definitions.Def_WeightedCache3SUM_Alias_b15542bf609bcf98
import Definitions.Def_WeightedCache3SUM_Alias_362a3b2d8940306a
import Definitions.Def_WeightedCache3SUM_Alias_40e937d67ef507b4
import Definitions.Def_WeightedCache3SUM_Alias_dfc7d85d435022ae
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
open ThreeSum ThreeSum.LightReportingCatalogQuery
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixCatalog ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostCatalogSelection
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.LightReportingCatalogQuery.program_meets_w3sum_ac885d1
    {μ : ℕ → ℤ} {h J k t baseL baseR boxCut boxBase indexBase ptrBase maskBase work depth : ℕ}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512*h)))) (hk : k ≤ J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdataL : baseL+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ maskBase)
    (hdataR : baseR+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ maskBase)
    (hindex : indexBase+count h k ≤ maskBase) (hptr : ptrBase+count h k ≤ maskBase)
    (hboxesEnd : boxBase+count h k*stride (suffixStage J (512*h) k) boxCut ≤ maskBase)
    (hmasks : maskBase+LightSparseQuery.queryItems (residualSize h J k) t ≤ work)
    (hspace : work+1+tableSize (width h J)+(width h J+1) ≤ lim.space)
    (hpowSpace : work+(2*width h J+2) ≤ lim.space)
    (hemodSpace : work+(Nat.log 2 (LightReportingCatalogLookup.valueBound (width h J) (count h k)+1)+2) ≤ lim.space)
    (hword : (((width h J+1)*2^(width h J+1) : ℕ) : ℤ) ≤ lim.word)
    (hlookupWord : (LightReportingCatalogLookup.word (width h J) (count h k) : ℤ) ≤ lim.word)
    (hvalueWord : (LightSparseQuery.magnitudeBound (suffixStage J (512*h) k) (suffixStage J (512*h) k)
      (residualSize h J k) t B.card C.card : ℤ) ≤ lim.word)
    (ht : t ≤ residualSize h J k+1) (hboxCut : boxCut ≤ residualSize h J k)
    (hflags : residualSize h J k-t ≤ boxCut)
    (hstoredL : LightZetaStages.StoredThrough μ baseL (sourceCut h J)
      (leftSource pMod B b w.2.2) (width h J))
    (hstoredR : LightZetaStages.StoredThrough μ baseR (sourceCut h J)
      (rightSource pMod shift C c w.2.2) (width h J))
    (hindexData : ∃ S : List ℤ, Seg μ indexBase S ∧
      S.Perm (ReportingHostPackedCatalog.codes (ReportingHostPackedCatalog.prefixKey h J k) (count h k)) ∧
      S.Pairwise (· ≤ ·))
    (hptrs : SegN μ ptrBase (List.ofFn fun i : Fin (count h k) =>
      boxBase+i.val*stride (suffixStage J (512*h) k) boxCut))
    (hboxes : ∀ i < count h k, LightBoxStages.StoredThrough μ
      (boxBase+i*stride (suffixStage J (512*h) k) boxCut) boxCut
      (leafWeight (block_fit hk) (leftSource pMod B b w.2.2) (rightSource pMod shift C c w.2.2)
        (suffixStage J (512*h) k) (preL h J k i) (preR h J k i))
      (suffixStage J (512*h) k))
    (hd : depth+2*width h J+12 ≤ lim.depth) :
    Meets lim program 35 depth
      [width h J,sourceCut h J,suffixStage J (512*h) k,k*h,
        subsetMask (leftPrefix k (prefixRows (J := J) pre)),k*h,
        subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre)),
        suffixStage J (512*h) k,k*(512*h),residualSize h J k,subsetMask (querySet k (outputRows w.2.2)),
        t,baseL,baseR,boxCut,indexBase,ptrBase,count h k,maskBase,work]
      μ (time h J k t)
      (fun r μ' =>
        r = (prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℤ) ∧
        KeptBut μ μ' work maskBase (LightSparseQuery.queryItems (residualSize h J k) t)) := by sorry
