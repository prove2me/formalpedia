-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixMasks_positionalHash_ofFn
-- name    : ThreeSum.ReportingHostPrefixMasks.positionalHash_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:54:03.931568+00:00
-- url     : https://prove2.me/theorems/38b7c700-e4b9-4403-a9a8-6c08b49d27e5
-- title:
--   Reporting Host Prefix Masks: positional Hash of Fn
-- statement:
--   The Reporting Host Prefix Masks construction uses the positional Hash of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixMasks.lean#L24-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixMasks.lean#L24-L35

import Definitions.Def_Submission_ThreeSum_ReportingHostPairEnumeration
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixMasks
import Theorems.Thm_ThreeSum_BlockIndex_positionalHash_ofFn

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixMasks
open Finset ThreeSum.SubsetAddress BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open BlockForced
open ReportingHostPrefixCatalog ReportingHostPairEnumeration
open scoped BigOperators
set_option maxHeartbeats 500000
variable {α : Type*}

theorem ThreeSum.ReportingHostPrefixMasks.positionalHash_ofFn (p : ℤ) (raw : α → ℤ) {k : ℕ} (f : Fin k → α) :
    Radix.positionalHash p raw (List.ofFn f) = ∑ i : Fin k, p^i.val*raw (f i) := by sorry
