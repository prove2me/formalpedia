-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixMasks_leftHash_eq_mask
-- name    : ThreeSum.ReportingHostPrefixMasks.leftHash_eq_mask
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:54:34.805596+00:00
-- url     : https://prove2.me/theorems/b7bc6a92-e199-4e7a-9492-fd0f6599a56a
-- title:
--   Reporting Host Prefix Masks: left Hash eq mask
-- statement:
--   The Reporting Host Prefix Masks construction uses the left Hash eq mask property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixMasks.lean#L66-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixMasks.lean#L66-L73

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

theorem ThreeSum.ReportingHostPrefixMasks.leftHash_eq_mask {h J k : ℕ} (hk : k ≤ J) (p : Prefix h k) :
    Radix.positionalHash ((2^(512*h) : ℕ) : ℤ) (fun q => (subsetMask q.1 : ℤ)) (tuple p) =
      (subsetMask (leftSet (J := J) p) : ℤ) := by sorry
