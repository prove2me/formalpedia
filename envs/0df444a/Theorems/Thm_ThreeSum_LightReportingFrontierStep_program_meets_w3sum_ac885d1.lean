-- Prove2me | Theorems.Thm_ThreeSum_LightReportingFrontierStep_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightReportingFrontierStep.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:58:44.188376+00:00
-- url     : https://prove2.me/theorems/c751ce88-6d16-497e-b98e-7ae08b36d25a
-- title:
--   Light Reporting Frontier Step: program meets
-- statement:
--   The Light Reporting Frontier Step construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingFrontierStep.lean#L57-L247
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingFrontierStep.lean#L57-L247

import Definitions.Def_Submission_ThreeSum_LightReportingPositiveExpand
import Definitions.Def_Submission_ThreeSum_ReportingHostPositiveBatch
import Definitions.Def_Submission_ThreeSum_LightReportingFrontierStep
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightBlockBoxes_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_427f455cbe093cd3
import Theorems.Thm_ThreeSum_LightBlockChildren_program_meets
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
import Definitions.Def_WeightedCache3SUM_Alias_a2917ec7b7f9f23f
import Definitions.Def_WeightedCache3SUM_Alias_fc697fae61d94ff7
import Definitions.Def_WeightedCache3SUM_Alias_bb907f0b533f0452
import Definitions.Def_WeightedCache3SUM_Alias_fb2417efddae0cb5
import Definitions.Def_WeightedCache3SUM_Alias_7f1c96094f5b1c13
import Definitions.Def_WeightedCache3SUM_Alias_00b35c3259394183
import Theorems.Thm_ThreeSum_LightReportingFilter_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_781f7abf8592a079
import Theorems.Thm_ThreeSum_LightReportingGather_program_meets
import Theorems.Thm_ThreeSum_LightReportingPackKeys_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_8a2cd73670b38080
import Definitions.Def_WeightedCache3SUM_Alias_bfa505cca5c6af3f
import Definitions.Def_WeightedCache3SUM_Alias_9e2aececf85d8818
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
open ThreeSum ThreeSum.LightReportingFrontierStep
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
open ReportingHostMasks LightBlockChildrenIndexed ReportingHostPositive ReportingHostPositiveBatch
open LightReportingPositiveExpand
set_option maxHeartbeats 3500000
set_option maxRecDepth 10000
variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.LightReportingFrontierStep.program_meets_w3sum_ac885d1
    {μ : ℕ → ℤ} {h J k t baseL baseR boxCut boxBase indexBase ptrBase inL inR outL outR masks dstL dstR dst selected maskBase work depth : ℕ}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pres : List (List (Finset (Fin (512*h))))) (hk : k < J)
    (hp : ∀ pre ∈ pres, ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdataL : baseL+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ outL)
    (hdataR : baseR+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ outL)
    (hindex : indexBase+count h (k+1) ≤ outL) (hptr : ptrBase+count h (k+1) ≤ outL)
    (hboxesEnd : boxBase+count h (k+1)*stride (suffixStage J (512*h) (k+1)) boxCut ≤ outL)
    (hinL : inL+pres.length ≤ outL) (hinR : inR+pres.length ≤ outL)
    (houtL : outL+pres.length*groupSize h ≤ outR) (houtR : outR+pres.length*groupSize h ≤ masks)
    (hmasks : masks+groupSize h ≤ dstL) (hleft : dstL+groupSize h ≤ dstR)
    (hright : dstR+groupSize h ≤ dst) (hdst : dst+groupSize h ≤ selected)
    (hselected : selected+groupSize h ≤ maskBase)
    (hqueryMasks : maskBase+LightSparseQuery.queryItems (residualSize h J (k+1)) t ≤ work)
    (hspace : work+1+tableSize (width h J)+(width h J+1) ≤ lim.space)
    (hpowSpace : work+(2*width h J+2) ≤ lim.space)
    (hemodSpace : work+(Nat.log 2 (LightReportingCatalogLookup.valueBound (width h J) (count h (k+1))+1)+2) ≤ lim.space)
    (hword : (((width h J+1)*2^(width h J+1) : ℕ) : ℤ) ≤ lim.word)
    (hlookupWord : (LightReportingCatalogLookup.word (width h J) (count h (k+1)) : ℤ) ≤ lim.word)
    (hvalueWord : (LightSparseQuery.magnitudeBound (suffixStage J (512*h) (k+1)) (suffixStage J (512*h) (k+1))
      (residualSize h J (k+1)) t B.card C.card : ℤ) ≤ lim.word)
    (ht : t ≤ residualSize h J (k+1)+1) (hboxCut : boxCut ≤ residualSize h J (k+1))
    (hflags : residualSize h J (k+1)-t ≤ boxCut)
    (hstoredL : LightZetaStages.StoredThrough μ baseL (sourceCut h J)
      (leftSource pMod B b w.2.2) (width h J))
    (hstoredR : LightZetaStages.StoredThrough μ baseR (sourceCut h J)
      (rightSource pMod shift C c w.2.2) (width h J))
    (hindexData : ∃ S : List ℤ, Seg μ indexBase S ∧
      S.Perm (ReportingHostPackedCatalog.codes (ReportingHostPackedCatalog.prefixKey h J (k+1)) (count h (k+1))) ∧
      S.Pairwise (· ≤ ·))
    (hptrs : SegN μ ptrBase (List.ofFn fun i : Fin (count h (k+1)) =>
      boxBase+i.val*stride (suffixStage J (512*h) (k+1)) boxCut))
    (hboxes : ∀ i < count h (k+1), LightBoxStages.StoredThrough μ
      (boxBase+i*stride (suffixStage J (512*h) (k+1)) boxCut) boxCut
      (leafWeight (block_fit (Nat.succ_le_of_lt hk)) (leftSource pMod B b w.2.2) (rightSource pMod shift C c w.2.2)
        (suffixStage J (512*h) (k+1)) (preL h J (k+1) i) (preR h J (k+1) i))
      (suffixStage J (512*h) (k+1)))
    (hparentsL : SegN μ inL (pres.map fun pre => subsetMask (leftPrefix k (prefixRows (J := J) pre))))
    (hparentsR : SegN μ inR (pres.map fun pre =>
      subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre))))
    (hd : depth+2*width h J+17 ≤ lim.depth) :
    Meets lim program 50 depth
      [width h J,h,rowMask (outputRows w.2.2) ⟨k,hk⟩,subsetMask (querySet k (outputRows w.2.2)),
        masks,dstL,dstR,work,sourceCut h J,suffixStage J (512*h) (k+1),(k+1)*h,residualSize h J (k+1),
        t,baseL,baseR,boxCut,indexBase,ptrBase,count h (k+1),groupSize h,dst,selected,maskBase,(k+1)*(512*h),
        inL,inR,pres.length,outL,outR]
      μ (time h J k t pres.length)
      (fun r ν =>
        let next := pres.flatMap (fun pre => positiveChildren (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w pre hk)
        r = (next.length : ℤ) ∧
        SegN ν outL (next.map fun pre => subsetMask (leftPrefix (k+1) (prefixRows (J := J) pre))) ∧
        SegN ν outR (next.map fun pre =>
          subsetMask (rightPrefix (k+1) (outputRows w.2.2) (prefixRows (J := J) pre))) ∧
        KeptOutputs μ ν masks outL outR next.length) := by sorry
