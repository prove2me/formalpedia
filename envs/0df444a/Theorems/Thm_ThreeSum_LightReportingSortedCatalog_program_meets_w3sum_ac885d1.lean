-- Prove2me | Theorems.Thm_ThreeSum_LightReportingSortedCatalog_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightReportingSortedCatalog.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:15:34.228684+00:00
-- url     : https://prove2.me/theorems/a11d115a-40f5-4d91-a6c8-ad4b51a69e46
-- title:
--   Light Reporting Sorted Catalog: program meets
-- statement:
--   The Light Reporting Sorted Catalog construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSortedCatalog.lean#L33-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingSortedCatalog.lean#L33-L87

import Definitions.Def_Submission_ThreeSum_LightReportingPackKeys
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Definitions.Def_Submission_ThreeSum_LightReportingSortedCatalog
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
import Theorems.Thm_ThreeSum_LightReportingPackKeys_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_8a2cd73670b38080
import Definitions.Def_WeightedCache3SUM_Alias_f4a3749c14d0f5f9
import Definitions.Def_WeightedCache3SUM_Alias_a2387e9e7b890e99
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
open ThreeSum ThreeSum.LightReportingSortedCatalog
open Light ThreeSum.LightPascal ThreeSum.LightSubsetAddress ReportingHostPackedCatalog
variable {lim : Limits}

theorem ThreeSum.LightReportingSortedCatalog.program_meets_w3sum_ac885d1 {μ : ℕ → ℤ} {W inL inR n dst work d : ℕ}
    (left right : ℕ → ℕ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hleft : inL+n ≤ dst) (hright : inR+n ≤ dst) (hdst : dst+n ≤ work)
    (hpowSpace : work+(W+1) ≤ lim.space) (hsortSpace : work+n ≤ lim.space)
    (hword : (word W n : ℤ) ≤ lim.word)
    (hreadL : ∀ i < n, μ (inL+i) = (left i : ℤ))
    (hreadR : ∀ i < n, μ (inR+i) = (right i : ℤ))
    (hboundL : ∀ i < n, left i < 2^W) (hboundR : ∀ i < n, right i < 2^W)
    (hd : d+Nat.clog 2 n+2 ≤ lim.depth) :
    Meets lim program 6 d [W,inL,inR,n,dst,work] μ (time W n)
      (fun _ μ' =>
        (∃ S : List ℤ, Seg μ' dst S ∧ S.Perm (codes (fun i => pairKey (2^W) (left i) (right i)) n) ∧
          S.Pairwise (· ≤ ·)) ∧ Kept μ μ' dst) := by sorry
