-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixMasks_rightHash_eq_mask
-- name    : ThreeSum.ReportingHostPrefixMasks.rightHash_eq_mask
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:54:29.950503+00:00
-- url     : https://prove2.me/theorems/da3a5c4a-256c-482d-9a43-8b51a632b17c
-- title:
--   Reporting Host Prefix Masks: right Hash eq mask
-- statement:
--   The Reporting Host Prefix Masks construction uses the right Hash eq mask property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixMasks.lean#L75-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixMasks.lean#L75-L82

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

theorem ThreeSum.ReportingHostPrefixMasks.rightHash_eq_mask {h J k : ℕ} (hk : k ≤ J) (p : Prefix h k) :
    Radix.positionalHash ((2^(512*h) : ℕ) : ℤ) (fun q => (subsetMask q.2 : ℤ)) (tuple p) =
      (subsetMask (rightSet (J := J) p) : ℤ) := by sorry
