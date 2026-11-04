-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankHeader_header_length
-- name    : ThreeSum.SharedReportingBankHeader.header_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:57:19.205919+00:00
-- url     : https://prove2.me/theorems/7935c0be-4a1f-4e05-9813-2bf56e43b989
-- title:
--   Shared Reporting Bank Header: header length
-- statement:
--   The Shared Reporting Bank Header construction uses the header length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankHeader.lean#L29-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankHeader.lean#L29-L29

import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankHeader
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankHeader
open Light GlobalEncoding SharedReportingBankRows SharedReportingBankLevels
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1900000

theorem ThreeSum.SharedReportingBankHeader.header_length (free h J NB NC g : ℕ) : (header free h J NB NC g).length=9 := by sorry
