-- Prove2me | Theorems.Thm_ThreeSum_LightReportingSuffixQueryIndexed_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightReportingSuffixQueryIndexed.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:41:43.475969+00:00
-- url     : https://prove2.me/theorems/06675b97-72cc-40f5-b2ed-d89c89cbefdb
-- title:
--   Light Reporting Suffix Query Indexed: program meets
-- statement:
--   The Light Reporting Suffix Query Indexed construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixQueryIndexed.lean#L17-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixQueryIndexed.lean#L17-L79

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixQueryHost
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBoxes
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixQueryIndexed
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
import Theorems.Thm_ThreeSum_LightReportingSuffixBoxes_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_362a3b2d8940306a
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

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixQueryIndexed
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix
variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.LightReportingSuffixQueryIndexed.program_meets_w3sum_ac885d1
    {μ : ℕ → ℤ} {h J k t baseL baseR boxCut boxBase maskBase work depth : ℕ}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512*h)))) (hk : k ≤ J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdataL : baseL+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ maskBase)
    (hdataR : baseR+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ maskBase)
    (hdataBox : boxBase+(suffixStage J (512*h) k+1)*downsetCap (suffixStage J (512*h) k) boxCut ≤ maskBase)
    (hmasks : maskBase+LightSparseQuery.queryItems (residualSize h J k) t ≤ work)
    (hspace : work+1+tableSize (width h J)+(width h J+1) ≤ lim.space)
    (hword : (((width h J+1)*2^(width h J+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : (LightSparseQuery.magnitudeBound (suffixStage J (512*h) k) (suffixStage J (512*h) k)
      (residualSize h J k) t B.card C.card : ℤ) ≤ lim.word)
    (ht : t ≤ residualSize h J k+1) (hboxCut : boxCut ≤ residualSize h J k)
    (hflags : residualSize h J k-t ≤ boxCut)
    (hstoredL : LightZetaStages.StoredThrough μ baseL (sourceCut h J)
      (leftSource pMod B b w.2.2) (width h J))
    (hstoredR : LightZetaStages.StoredThrough μ baseR (sourceCut h J)
      (rightSource pMod shift C c w.2.2) (width h J))
    (hstoredBox : LightBoxStages.StoredThrough μ boxBase boxCut
      (LightReportingSuffixBoxes.localLeaf hk pMod shift B C b c w.2.2 pre) (suffixStage J (512*h) k))
    (hd : depth+width h J+10 ≤ lim.depth) :
    Meets lim LightReportingSuffixQueryHost.program 30 depth
      [width h J,sourceCut h J,suffixStage J (512*h) k,k*h,
        subsetMask (leftPrefix k (prefixRows (J := J) pre)),k*h,
        subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre)),
        suffixStage J (512*h) k,k*(512*h),residualSize h J k,subsetMask (querySet k (outputRows w.2.2)),
        t,baseL,baseR,boxCut,boxBase,maskBase,work]
      μ (LightReportingSuffixQueryHost.time (width h J) (suffixStage J (512*h) k) (residualSize h J k) t)
      (fun r μ' =>
        r = (prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℤ) ∧
        KeptBut μ μ' work maskBase (LightSparseQuery.queryItems (residualSize h J k) t)) := by sorry
