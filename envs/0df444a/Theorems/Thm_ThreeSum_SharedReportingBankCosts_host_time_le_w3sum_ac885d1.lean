-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankCosts_host_time_le_w3sum_ac885d1
-- name    : ThreeSum.SharedReportingBankCosts.host_time_le_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:10:46.504082+00:00
-- url     : https://prove2.me/theorems/752c8927-d802-4d4f-82b9-87676c4f7756
-- title:
--   Shared Reporting Bank Costs: host time le
-- statement:
--   The Shared Reporting Bank Costs construction uses the host time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankCosts.lean#L102-L115
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankCosts.lean#L102-L115

import Definitions.Def_Submission_ThreeSum_LightSharedReportingHost
import Definitions.Def_Submission_ThreeSum_LightSwitchCosts
import Definitions.Def_Submission_ThreeSum_SharedReportingBankCosts
set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankCosts
open Scales Parameters StageBounds ArithmeticStageBounds CostLedger Filter
open SharedReportingCosts
open scoped Topology
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

theorem ThreeSum.SharedReportingBankCosts.host_time_le_w3sum_ac885d1 {NB NC n : ℕ} (hB : NB ≤ n) (hC : NC ≤ n) :
    LightSharedReportingHost.time (half n) (blocks n) NB NC (BandScales.bandSize n) ≤ budget n := by sorry
