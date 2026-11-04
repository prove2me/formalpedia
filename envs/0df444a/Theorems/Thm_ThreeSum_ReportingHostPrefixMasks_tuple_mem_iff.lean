-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixMasks_tuple_mem_iff
-- name    : ThreeSum.ReportingHostPrefixMasks.tuple_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:54:49.567311+00:00
-- url     : https://prove2.me/theorems/3c9e51d3-4319-4f00-b492-3603d6a789c6
-- title:
--   Reporting Host Prefix Masks: tuple mem iff
-- statement:
--   The Reporting Host Prefix Masks construction uses the tuple mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixMasks.lean#L112-L119
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixMasks.lean#L112-L119

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

theorem ThreeSum.ReportingHostPrefixMasks.tuple_mem_iff {h k : ℕ} (xs : List (Finset (Fin (512*h)) × Finset (Fin (512*h)))) :
    xs ∈ RadixKeyLists.tuples (pairs (512*h) h) k ↔ ∃ p : Prefix h k, tuple p = xs := by sorry
