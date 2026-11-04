-- Prove2me | Theorems.Thm_ThreeSum_SharedReportingBankCosts_cut_eq
-- name    : ThreeSum.SharedReportingBankCosts.cut_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:06:56.942616+00:00
-- url     : https://prove2.me/theorems/9eaf2b36-448d-47aa-9a0b-b669619059a1
-- title:
--   Shared Reporting Bank Costs: cut eq
-- statement:
--   The Shared Reporting Bank Costs construction uses the cut eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankCosts.lean#L35-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankCosts.lean#L35-L40

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

theorem ThreeSum.SharedReportingBankCosts.cut_eq (n k : ℕ) :
    SharedReportingBankLevels.boxCut (half n) (blocks n) k=
      Switch.residualSize n k-Switch.actualSwitch n k := by sorry
