-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixMasks_leftSet_mask
-- name    : ThreeSum.ReportingHostPrefixMasks.leftSet_mask
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:53:27.755615+00:00
-- url     : https://prove2.me/theorems/fe0c75c0-dbc2-48e8-bbb8-cee1cbacedfe
-- title:
--   Reporting Host Prefix Masks: left Set mask
-- statement:
--   The Reporting Host Prefix Masks construction uses the left Set mask property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixMasks.lean#L56-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixMasks.lean#L56-L59

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

theorem ThreeSum.ReportingHostPrefixMasks.leftSet_mask {h J k : ℕ} (hk : k ≤ J) (p : Prefix h k) :
    subsetMask (leftSet (J := J) p) = ∑ i : Fin k, 2^(i.val*(512*h))*subsetMask (p i).val.1 := by sorry
