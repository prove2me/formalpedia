-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixMasks_maskPair_injective_w3sum_ac885d1
-- name    : ThreeSum.ReportingHostPrefixMasks.maskPair_injective_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:54:50.709852+00:00
-- url     : https://prove2.me/theorems/9d9b15d4-c179-48e4-9fc7-22c840670355
-- title:
--   Reporting Host Prefix Masks: mask Pair injective
-- statement:
--   The Reporting Host Prefix Masks construction uses the mask Pair injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixMasks.lean#L121-L135
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixMasks.lean#L121-L135

import Definitions.Def_Submission_ThreeSum_ReportingHostPairEnumeration
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixMasks
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixMasks
open Finset ThreeSum.SubsetAddress BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open BlockForced
open ReportingHostPrefixCatalog ReportingHostPairEnumeration
open scoped BigOperators
set_option maxHeartbeats 500000
variable {α : Type*}

theorem ThreeSum.ReportingHostPrefixMasks.maskPair_injective_w3sum_ac885d1 {h J k : ℕ} (hk : k ≤ J) :
    Function.Injective (fun p : Prefix h k =>
      (subsetMask (leftSet (J := J) p),subsetMask (rightSet (J := J) p))) := by sorry
