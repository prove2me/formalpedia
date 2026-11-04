-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixMasks_rightSet_mask
-- name    : ThreeSum.ReportingHostPrefixMasks.rightSet_mask
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:54:34.338564+00:00
-- url     : https://prove2.me/theorems/878bd998-7487-40a1-b316-d5f1b08148ee
-- title:
--   Reporting Host Prefix Masks: right Set mask
-- statement:
--   The Reporting Host Prefix Masks construction uses the right Set mask property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixMasks.lean#L61-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixMasks.lean#L61-L64

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

theorem ThreeSum.ReportingHostPrefixMasks.rightSet_mask {h J k : ℕ} (hk : k ≤ J) (p : Prefix h k) :
    subsetMask (rightSet (J := J) p) = ∑ i : Fin k, 2^(i.val*(512*h))*subsetMask (p i).val.2 := by sorry
