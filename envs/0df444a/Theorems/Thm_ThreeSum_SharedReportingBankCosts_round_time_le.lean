-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankCosts_round_time_le
-- name    : ThreeSum.SharedReportingBankCosts.round_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:10:03.331216+00:00
-- url     : https://prove2.me/theorems/5f0e9a44-eaf1-4c79-a6d7-b5066c50e17b
-- title:
--   Shared Reporting Bank Costs: round time le
-- statement:
--   The Shared Reporting Bank Costs construction uses the round time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankCosts.lean#L44-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankCosts.lean#L44-L66

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

theorem ThreeSum.SharedReportingBankCosts.round_time_le {n k : ℕ} (hk : k ≤ blocks n) :
    LightSharedReportingLevels.roundTime (half n) (blocks n) k+8 ≤
      roundOverhead n*prefixBoxes n k := by sorry
