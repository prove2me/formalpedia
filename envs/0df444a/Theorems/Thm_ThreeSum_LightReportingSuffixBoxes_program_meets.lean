-- Prove2me | Theorems.Thm_ThreeSum_LightReportingSuffixBoxes_program_meets
-- name    : ThreeSum.LightReportingSuffixBoxes.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:33:32.97361+00:00
-- url     : https://prove2.me/theorems/9df219bf-06b4-4ee1-9560-a35315635e63
-- title:
--   Light Reporting Suffix Boxes: program meets
-- statement:
--   The Light Reporting Suffix Boxes construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixBoxes.lean#L24-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSuffixBoxes.lean#L24-L83

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixBoxes
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
open ThreeSum ThreeSum.LightReportingSuffixBoxes
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds LightBlockQuery ReportingHostSuffix
variable {lim : Limits}
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.LightReportingSuffixBoxes.program_meets {μ : ℕ → ℤ} {h J k baseL baseR boxCut boxBase maskBase work depth : ℕ}
    (pMod shift : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hk : k ≤ J) (hp : ValidPrefix q k pre)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdataL : baseL+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ boxBase)
    (hdataR : baseR+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ boxBase)
    (hbox : boxBase+(suffixStage J (512*h) k+1)*downsetCap (suffixStage J (512*h) k) boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap (suffixStage J (512*h) k) boxCut ≤ work)
    (hspace : work+1+tableSize (width h J)+(width h J+1) ≤ lim.space)
    (hword : (((width h J+1)*2^(width h J+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^(suffixStage J (512*h) k)*
      ((2^(suffixStage J (512*h) k)*B.card)*(2^(suffixStage J (512*h) k)*C.card)) : ℕ) : ℤ) ≤ lim.word)
    (hboxCut : boxCut ≤ residualSize h J k)
    (hstoredL : LightZetaStages.StoredThrough μ baseL (sourceCut h J)
      (leftSource pMod B b q) (width h J))
    (hstoredR : LightZetaStages.StoredThrough μ baseR (sourceCut h J)
      (rightSource pMod shift C c q) (width h J))
    (hd : depth+width h J+11 ≤ lim.depth) :
    Meets lim LightReportingSuffixSetup.program 29 depth
      [width h J,sourceCut h J,boxCut,suffixStage J (512*h) k,k*h,
        subsetMask (leftPrefix k (prefixRows (J := J) pre)),k*h,
        subsetMask (rightPrefix k (outputRows q) (prefixRows (J := J) pre)),
        suffixStage J (512*h) k,k*(512*h),baseL,baseR,boxBase,maskBase,work]
      μ (LightReportingSuffixSetup.time (width h J) (suffixStage J (512*h) k) boxCut (k*(512*h)))
      (fun _ μ' =>
        LightBoxStages.StoredThrough μ' boxBase boxCut (localLeaf hk pMod shift B C b c q pre)
          (suffixStage J (512*h) k) ∧
        LightZetaStages.StoredThrough μ' baseL (sourceCut h J) (leftSource pMod B b q) (width h J) ∧
        LightZetaStages.StoredThrough μ' baseR (sourceCut h J) (rightSource pMod shift C c q) (width h J) ∧
        KeptBut μ μ' maskBase boxBase
          ((suffixStage J (512*h) k+1)*downsetCap (suffixStage J (512*h) k) boxCut)) := by sorry
