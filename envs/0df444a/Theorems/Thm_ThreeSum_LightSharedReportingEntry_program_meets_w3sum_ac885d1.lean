-- Prove2me | Theorems.Thm_ThreeSum_LightSharedReportingEntry_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSharedReportingEntry.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:12:47.644003+00:00
-- url     : https://prove2.me/theorems/a86bc974-06ac-48ab-9e57-13802f3a5405
-- title:
--   Light Shared Reporting Entry: program meets
-- statement:
--   The Light Shared Reporting Entry construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSharedReportingEntry.lean#L42-L145
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSharedReportingEntry.lean#L42-L145

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_LightSharedReportingEntry
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
import Definitions.Def_WeightedCache3SUM_Alias_0d2857ef7f97fcc6
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
open ThreeSum ThreeSum.LightSharedReportingEntry
open Light SubsetAddress LightPascal ReportingHostSuffix ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
open SharedReportingBankData
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000

theorem ThreeSum.LightSharedReportingEntry.program_meets_w3sum_ac885d1 {lim : Limits} {μ : ℕ → ℤ}
    {h J k cut boxCut baseL baseR cellL cellR srcS pairL pairR stageL stageR
      ptrBase boxBase maskBase indexBase work B D d t rec : ℕ}
    (hk : k ≤ J) (f g : Finset (Fin (J*(512*h))) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hcut : cut ≤ J*(512*h)) (hboxCut : boxCut ≤ (J-k)*(512*h))
    (hcellL : cellL < rec) (hcellR : cellR < rec)
    (hdataL : baseL+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ rec)
    (hdataR : baseR+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ rec)
    (hrec : rec+5 ≤ srcS)
    (hS : srcS+(512*h).choose h ≤ pairL)
    (hL : pairL+LightReportingPrefixArrays.localCount (512*h) h ≤ pairR)
    (hR : pairR+LightReportingPrefixArrays.localCount (512*h) h ≤ stageL)
    (hstageL : LightRadixKeys.space stageL (LightReportingPrefixArrays.localCount (512*h) h) k ≤ stageR)
    (hstageR : LightRadixKeys.space stageR (LightReportingPrefixArrays.localCount (512*h) h) k ≤ ptrBase)
    (hptr : ptrBase+count h k ≤ boxBase)
    (hbox : boxBase+count h k*stride ((J-k)*(512*h)) boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap ((J-k)*(512*h)) boxCut ≤ work)
    (hindex : maskBase ≤ indexBase) (hindexEnd : indexBase+count h k ≤ work)
    (hpairSpace : work+2*(512*h)+2 ≤ lim.space)
    (hspace : work+1+tableSize (J*(512*h))+(J*(512*h)+1) ≤ lim.space)
    (hsortSpace : work+count h k ≤ lim.space)
    (hpowWord : ((2^(512*h+1) : ℕ) : ℤ) ≤ lim.word)
    (hkeysWord : (LightRadixKeys.word (2^(512*h)) (2^(512*h)) k : ℤ) ≤ lim.word)
    (hword : (((J*(512*h)+1)*2^(J*(512*h)+1) : ℕ) : ℤ) ≤ lim.word)
    (hindexWord : (LightReportingSortedCatalog.word (J*(512*h)) (count h k) : ℤ) ≤ lim.word)
    (hvalueWord : (((2^((J-k)*(512*h))*
      ((2^((J-k)*(512*h))*B)*(2^((J-k)*(512*h))*D))) : ℕ) : ℤ) ≤ lim.word)
    (htWord : (t : ℤ) ≤ lim.word)
    (hpre : k*h+boxCut ≤ cut) (hf : ∀ S, S.card ≤ cut → |f S| ≤ B)
    (hg : ∀ S, S.card ≤ cut → |g S| ≤ D)
    (hleftRead : μ cellL=(baseL : ℤ)) (hrightRead : μ cellR=(baseR : ℤ))
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f (J*(512*h)))
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g (J*(512*h)))
    (hdPair : d+512*h+k+7 ≤ lim.depth) (hd : d+J*(512*h)+16 ≤ lim.depth)
    (hdSort : d+Nat.clog 2 (count h k)+4 ≤ lim.depth) :
    Meets lim program 52 d
      [J*(512*h),cut,boxCut,(J-k)*(512*h),(J-k)*(512*h),k*(512*h),cellL,cellR,
        512*h,h,k,srcS,pairL,pairR,stageL,stageR,ptrBase,boxBase,maskBase,work,indexBase,t,rec]
      μ (time h J k boxCut) (fun r ν =>
        r=(count h k : ℤ) ∧
        Entry ν rec ⟨t,boxCut,boxBase,indexBase,ptrBase⟩ hk f g ∧
        LightZetaStages.StoredThrough ν baseL cut f (J*(512*h)) ∧
        LightZetaStages.StoredThrough ν baseR cut g (J*(512*h)) ∧
        KeptBut μ ν srcS rec 5) := by sorry
