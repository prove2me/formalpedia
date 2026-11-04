-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostMasks_localChildren_length
-- name    : ThreeSum.ReportingHostMasks.localChildren_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:51:00.198211+00:00
-- url     : https://prove2.me/theorems/9f98558d-fff9-4831-9f70-6f81908cc5e1
-- title:
--   Reporting Host Masks: local Children length
-- statement:
--   The Reporting Host Masks construction uses the local Children length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostMasks.lean#L104-L106
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostMasks.lean#L104-L106

import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_ReportingHostMasks
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostMasks
open Finset BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open ThreeSum.SubsetAddress StoredReporting BlockForced

theorem ThreeSum.ReportingHostMasks.localChildren_length {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (localChildren i Q h).length = Q.card.choose h := by sorry
