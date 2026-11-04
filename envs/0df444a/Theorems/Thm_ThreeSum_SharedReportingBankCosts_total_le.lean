-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankCosts_total_le
-- name    : ThreeSum.SharedReportingBankCosts.total_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:09:45.210911+00:00
-- url     : https://prove2.me/theorems/79d7b48f-7e3f-40f0-beb9-0594cc3fa6e1
-- title:
--   Shared Reporting Bank Costs: total le
-- statement:
--   The Shared Reporting Bank Costs construction uses the total le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankCosts.lean#L88-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankCosts.lean#L88-L100

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

theorem ThreeSum.SharedReportingBankCosts.total_le {NB NC n : ℕ} (hB : NB ≤ n) (hC : NC ≤ n) :
    SharedReportingBankRows.total (half n) (blocks n) NB NC (BandScales.bandSize n) ≤
      3*bandCount n^2*TrimScales.scheduleCount n := by sorry
