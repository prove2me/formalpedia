-- Prove2me | Theorems.Thm_ThreeSum_LightSharedReportingLevels_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSharedReportingLevels.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T18:40:59.499288+00:00
-- url     : https://prove2.me/theorems/ee8fb4dc-76c9-4a8f-a85b-cf28fcfddc6c
-- title:
--   Light Shared Reporting Levels: program meets
-- statement:
--   The Light Shared Reporting Levels construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSharedReportingLevels.lean#L68-L198
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSharedReportingLevels.lean#L68-L198

import Definitions.Def_Submission_ThreeSum_LightSharedReportingCell
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
import Definitions.Def_Submission_ThreeSum_LightSharedReportingLoop
import Definitions.Def_Submission_ThreeSum_LightSharedReportingLevels
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
import Definitions.Def_WeightedCache3SUM_Alias_9ec307913a0c2e1a
import Definitions.Def_WeightedCache3SUM_Alias_70e2e63cbf342643
import Theorems.Thm_ThreeSum_LightSign_program_meets
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafGeneral_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeafTable_program_meets
import Theorems.Thm_ThreeSum_LightSignedLeaf_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets
import Theorems.Thm_ThreeSum_LightSparseQuery_program_meets
import Theorems.Thm_ThreeSum_LightStageLookup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightSubsetSetup_program_meets
import Theorems.Thm_ThreeSum_LightSwitchDepth_program_meets
import Theorems.Thm_ThreeSum_LightSwitch_program_meets
import Theorems.Thm_ThreeSum_LightWeightedEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightZetaCell_program_meets
import Theorems.Thm_ThreeSum_LightZetaPass_program_meets
import Theorems.Thm_ThreeSum_LightZetaStages_program_meets
import Theorems.Thm_ThreeSum_ReportingHostPairSegments_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightSharedReportingLevels
open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData SharedReportingBankLevels
set_option maxHeartbeats 3000000
set_option maxRecDepth 14000

theorem ThreeSum.LightSharedReportingLevels.program_meets_w3sum_ac885d1 {lim : Limits} {μ : ℕ → ℤ}
    {record base h J K baseL baseR cellL cellR B D d : ℕ}
    (f g : Finset (Fin (J*(512*h))) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hK : K ≤ LightSwitchDepth.depth J+1)
    (hrecords : record+5*K ≤ base)
    (hcellL : cellL < record) (hcellR : cellR < record)
    (hdataL : baseL+(J*(512*h)+1)*downsetCap (J*(512*h)) (2*h*J) ≤ record)
    (hdataR : baseR+(J*(512*h)+1)*downsetCap (J*(512*h)) (2*h*J) ≤ record)
    (R : Resources lim base h J K B D d)
    (hf : ∀ S, S.card ≤ 2*h*J → |f S| ≤ B)
    (hg : ∀ S, S.card ≤ 2*h*J → |g S| ≤ D)
    (hleftRead : μ cellL=(baseL : ℤ)) (hrightRead : μ cellR=(baseR : ℤ))
    (hstoredL : LightZetaStages.StoredThrough μ baseL (2*h*J) f (J*(512*h)))
    (hstoredR : LightZetaStages.StoredThrough μ baseR (2*h*J) g (J*(512*h))) :
    Meets lim program 64 d
      [h,J,K,cellL,cellR,localChoose h,localPairs h,record,base] μ (time h J K)
      (fun result ν => result=(baseAt base h J K : ℤ) ∧
        Built ν record base h J K f g ∧ Kept μ ν record ∧ KeptBut μ ν base record (5*K)) := by sorry
