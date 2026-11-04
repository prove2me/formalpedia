-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankHeader_payload_le_finish
-- name    : ThreeSum.SharedReportingBankHeader.payload_le_finish
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:38:06.943485+00:00
-- url     : https://prove2.me/theorems/6d151a20-11aa-4979-8fa2-3615f3ba1e67
-- title:
--   Shared Reporting Bank Header: payload le finish
-- statement:
--   The Shared Reporting Bank Header construction uses the payload le finish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankHeader.lean#L27-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankHeader.lean#L27-L28

import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankHeader
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankHeader
open Light GlobalEncoding SharedReportingBankRows SharedReportingBankLevels
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1900000

theorem ThreeSum.SharedReportingBankHeader.payload_le_finish (free h J NB NC g : ℕ) :
    payload free h J NB NC g ≤ finish free h J NB NC g := by sorry
