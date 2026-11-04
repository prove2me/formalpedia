-- Prove2me | Theorems.Thm_ThreeSum_LightReportingPositiveMasks_program_meets_w3sum_ac885d1
-- name    : ThreeSum.LightReportingPositiveMasks.program_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:30:42.445124+00:00
-- url     : https://prove2.me/theorems/0d707172-366b-449e-ae27-21025cae2c4d
-- title:
--   Light Reporting Positive Masks: program meets
-- statement:
--   The Light Reporting Positive Masks construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPositiveMasks.lean#L37-L102
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightReportingPositiveMasks.lean#L37-L102

import Definitions.Def_Submission_ThreeSum_LightReportingGatherPair
import Definitions.Def_Submission_ThreeSum_ReportingHostPositive
import Definitions.Def_Submission_ThreeSum_LightReportingPositiveMasks
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
open ThreeSum ThreeSum.LightReportingPositiveMasks
open Light Finset ThreeSum.SubsetAddress
open BlockRows BlockIndexedQuery BlockForced StoredReporting GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open LightBlockChildrenIndexed ReportingHostPositive
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem ThreeSum.LightReportingPositiveMasks.program_meets_w3sum_ac885d1 {μ : ℕ → ℤ} {h J k indices srcL srcR dstL dstR d : ℕ}
    (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (pre : List (Finset (Fin (512*h)))) (hk : k < J)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hindices : indices+(selectedIndices I w pre hk).length ≤ lim.space)
    (hsrcL : srcL+groupSize h ≤ lim.space) (hsrcR : srcR+groupSize h ≤ lim.space)
    (hdstL : dstL+(selectedIndices I w pre hk).length ≤ lim.space)
    (hdstR : dstR+(selectedIndices I w pre hk).length ≤ lim.space)
    (hsepIL : Apart indices (selectedIndices I w pre hk).length dstL (selectedIndices I w pre hk).length)
    (hsepIR : Apart indices (selectedIndices I w pre hk).length dstR (selectedIndices I w pre hk).length)
    (hsepLL : Apart srcL (groupSize h) dstL (selectedIndices I w pre hk).length)
    (hsepRL : Apart srcR (groupSize h) dstL (selectedIndices I w pre hk).length)
    (hsepRR : Apart srcR (groupSize h) dstR (selectedIndices I w pre hk).length)
    (hsepOut : Apart dstL (selectedIndices I w pre hk).length dstR (selectedIndices I w pre hk).length)
    (hreadI : SegN μ indices (selectedIndices I w pre hk))
    (hreadL : SegN μ srcL ((childPrefixes w.2.2 pre hk).map fun next =>
      subsetMask (leftPrefix (k+1) (prefixRows (J := J) next))))
    (hreadR : SegN μ srcR ((childPrefixes w.2.2 pre hk).map fun next =>
      subsetMask (rightPrefix (k+1) (outputRows w.2.2) (prefixRows (J := J) next))))
    (hword : ((2^(J*(512*h)+1) : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim LightReportingGatherPair.program 1 d
      [indices,srcL,srcR,(selectedIndices I w pre hk).length,groupSize h,dstL,dstR]
      μ (LightReportingGatherPair.time (selectedIndices I w pre hk).length)
      (fun _ ν =>
        SegN ν dstL ((positiveChildren I w pre hk).map fun next =>
          subsetMask (leftPrefix (k+1) (prefixRows (J := J) next))) ∧
        SegN ν dstR ((positiveChildren I w pre hk).map fun next =>
          subsetMask (rightPrefix (k+1) (outputRows w.2.2) (prefixRows (J := J) next))) ∧
        SameOutside2 μ ν dstL (selectedIndices I w pre hk).length dstR (selectedIndices I w pre hk).length) := by sorry
