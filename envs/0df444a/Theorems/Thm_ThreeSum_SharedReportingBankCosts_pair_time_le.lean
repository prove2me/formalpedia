-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankCosts_pair_time_le
-- name    : ThreeSum.SharedReportingBankCosts.pair_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:10:28.030617+00:00
-- url     : https://prove2.me/theorems/e79e3917-0987-43c0-aa69-b3753ca97949
-- title:
--   Shared Reporting Bank Costs: pair time le
-- statement:
--   The Shared Reporting Bank Costs construction uses the pair time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankCosts.lean#L73-L86
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankCosts.lean#L73-L86

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

theorem ThreeSum.SharedReportingBankCosts.pair_time_le (n : ℕ) :
    LightSharedReportingPair.time (half n) (blocks n) (SharedReportingBankHeader.levels (blocks n))+1000 ≤
      (roundOverhead n+1600)*allPrefixBoxes n := by sorry
