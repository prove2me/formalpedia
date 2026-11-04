-- Prove2me | Theorems.Thm_ThreeSum_LightReportingPrefixArrays_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightReportingPrefixArrays.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:23:02.624855+00:00
-- url     : https://prove2.me/theorems/14822800-316e-4a73-9281-74bcb951ea53
-- title:
--   Light Reporting Prefix Arrays: program meets
-- statement:
--   The Light Reporting Prefix Arrays construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPrefixArrays.lean#L38-L125
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPrefixArrays.lean#L38-L125

import Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixArrays
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
import Theorems.Thm_ThreeSum_LightReportingSuffixBoxes_program_meets
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
open ThreeSum ThreeSum.LightReportingPrefixArrays
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPairEnumeration ReportingHostPairSegments
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
variable {lim : Limits}

theorem ThreeSum.LightReportingPrefixArrays.program_meets_w3sum_ac885d1 {μ : ℕ → ℤ} {L h k srcS pairL pairR stageL stageR work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hh : 2*h ≤ L)
    (hS : srcS+L.choose h ≤ pairL)
    (hL : pairL+localCount L h ≤ pairR) (hR : pairR+localCount L h ≤ stageL)
    (hstageL : LightRadixKeys.space stageL (localCount L h) k ≤ stageR)
    (hstageR : LightRadixKeys.space stageR (localCount L h) k ≤ work)
    (hspace : work+2*L+2 ≤ lim.space)
    (hpowWord : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hkeysWord : (LightRadixKeys.word (2^L) (2^L) k : ℤ) ≤ lim.word)
    (hd : d+L+k+4 ≤ lim.depth) :
    Meets lim program 10 d [L,h,k,srcS,pairL,pairR,stageL,stageR,work] μ (time L h k)
      (fun r μ' =>
        r = (stageL+LightRadixKeys.offset (localCount L h) k : ℕ) ∧
        μ' (stageL+LightRadixKeys.offset (localCount L h) k) = ((localCount L h)^k : ℕ) ∧
        μ' (stageR+LightRadixKeys.offset (localCount L h) k) = ((localCount L h)^k : ℕ) ∧
        Seg μ' (stageL+LightRadixKeys.offset (localCount L h) k+1)
          (RadixKeyLists.values ((2^L : ℕ) : ℤ) (leftMasks L h) k) ∧
        Seg μ' (stageR+LightRadixKeys.offset (localCount L h) k+1)
          (RadixKeyLists.values ((2^L : ℕ) : ℤ) (rightMasks L h) k) ∧
        Kept μ μ' srcS) := by sorry
