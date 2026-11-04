-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_total_le
-- name    : ThreeSum.SharedReportingBankResourceBounds.total_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:28:09.440195+00:00
-- url     : https://prove2.me/theorems/f3a138ad-2287-4548-b04c-b6ce24459103
-- title:
--   Shared Reporting Bank Resource Bounds: total le
-- statement:
--   The Shared Reporting Bank Resource Bounds construction uses the total le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankResourceBounds.lean#L105-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankResourceBounds.lean#L105-L108

import Definitions.Def_Submission_ThreeSum_SharedReportingBankCosts
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBounds
import Theorems.Thm_ThreeSum_SharedReportingBankCosts_total_le

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Light SubsetAddress SharedReportingBankLayout SharedReportingBankLevels
open SharedReportingBankHeader SharedReportingBankRows
set_option maxHeartbeats 2800000
set_option maxRecDepth 14000

theorem ThreeSum.SharedReportingBankResourceBounds.total_le {NB NC n h J g : ℕ} (hB : NB ≤ n) (hC : NC ≤ n) :
    total h J NB NC g ≤ LightBlockSourceCatalog.count h J*n*n := by sorry
