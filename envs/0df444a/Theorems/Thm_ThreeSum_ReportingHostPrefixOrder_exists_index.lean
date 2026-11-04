-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostPrefixOrder_exists_index
-- name    : ThreeSum.ReportingHostPrefixOrder.exists_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:57:32.038023+00:00
-- url     : https://prove2.me/theorems/23ce666f-eafa-493e-9ac6-7977be92263f
-- title:
--   Reporting Host Prefix Order: exists index
-- statement:
--   The Reporting Host Prefix Order construction uses the exists index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixOrder.lean#L84-L88
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostPrefixOrder.lean#L84-L88

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixMasks
import Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixOrder
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPairEnumeration
open ReportingHostPrefixMasks ReportingHostPairSegments
set_option maxHeartbeats 600000

theorem ThreeSum.ReportingHostPrefixOrder.exists_index {h J k : ℕ} (p : Prefix h k) :
    ∃ i < (prefixes h k).length, preL h J k i = leftSet (J := J) p ∧
      preR h J k i = rightSet (J := J) p := by sorry
