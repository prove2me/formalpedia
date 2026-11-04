-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixMasks_tuple_mem
-- name    : ThreeSum.ReportingHostPrefixMasks.tuple_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:54:06.461761+00:00
-- url     : https://prove2.me/theorems/c979ef52-4b92-4767-a87b-368505eb4dd7
-- title:
--   Reporting Host Prefix Masks: tuple mem
-- statement:
--   The Reporting Host Prefix Masks construction uses the tuple mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixMasks.lean#L84-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixMasks.lean#L84-L90

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

theorem ThreeSum.ReportingHostPrefixMasks.tuple_mem {h k : ℕ} (p : Prefix h k) :
    tuple p ∈ RadixKeyLists.tuples (pairs (512*h) h) k := by sorry
