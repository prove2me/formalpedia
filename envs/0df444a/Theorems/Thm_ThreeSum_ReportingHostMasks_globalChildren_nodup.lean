-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostMasks_globalChildren_nodup
-- name    : ThreeSum.ReportingHostMasks.globalChildren_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:35:08.604409+00:00
-- url     : https://prove2.me/theorems/abd92b89-9a18-4b86-81f2-a6ce31352d31
-- title:
--   Reporting Host Masks: global Children nodup
-- statement:
--   The Reporting Host Masks construction uses the global Children nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostMasks.lean#L75-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostMasks.lean#L75-L76

import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_ReportingHostMasks
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostMasks
open Finset BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open ThreeSum.SubsetAddress StoredReporting BlockForced

theorem ThreeSum.ReportingHostMasks.globalChildren_nodup {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (globalChildren i Q h).Nodup := by sorry
