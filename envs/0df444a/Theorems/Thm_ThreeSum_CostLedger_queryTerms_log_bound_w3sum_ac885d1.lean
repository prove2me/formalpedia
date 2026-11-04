-- Prove2me | Theorems.Thm_ThreeSum_CostLedger_queryTerms_log_bound_w3sum_ac885d1
-- name    : ThreeSum.CostLedger.queryTerms_log_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:39:10.539719+00:00
-- url     : https://prove2.me/theorems/318c5304-4fa7-4645-bb71-59af0245c374
-- title:
--   Cost Ledger: query Terms log bound
-- statement:
--   The Cost Ledger construction uses the query Terms log bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/CostLedger.lean#L181-L213
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/CostLedger.lean#L181-L213

import Definitions.Def_Submission_ThreeSum_Switch
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_CostLedger
set_option autoImplicit false
open ThreeSum ThreeSum.CostLedger
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch
open scoped Topology BigOperators
set_option maxHeartbeats 400000
noncomputable section

theorem ThreeSum.CostLedger.queryTerms_log_bound_w3sum_ac885d1 {n j : ℕ} (hmu : 0 < mu n)
    (hj : j ≤ terminalDepth n) :
    Real.log (queryTerms n j : ℝ) ≤
      (mu n : ℝ) * Real.log 2 * (entropyRatio * (1 + boxSaving - 2 * bandShift)) +
        9 * entropyRatio * Real.log 2 := by sorry
