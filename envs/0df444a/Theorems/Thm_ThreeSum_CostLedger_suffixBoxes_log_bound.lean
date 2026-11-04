-- Prove2me | Theorems.Thm_ThreeSum_CostLedger_suffixBoxes_log_bound
-- name    : ThreeSum.CostLedger.suffixBoxes_log_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:38:31.803464+00:00
-- url     : https://prove2.me/theorems/88f2a4f9-80b5-4a62-9756-2c6ee462613d
-- title:
--   Cost Ledger: suffix Boxes log bound
-- statement:
--   The Cost Ledger construction uses the suffix Boxes log bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/CostLedger.lean#L107-L138
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/CostLedger.lean#L107-L138

import Definitions.Def_Submission_ThreeSum_Switch
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_CostLedger
set_option autoImplicit false
open ThreeSum ThreeSum.CostLedger
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch
open scoped Topology BigOperators
set_option maxHeartbeats 400000
noncomputable section

theorem ThreeSum.CostLedger.suffixBoxes_log_bound {n j : ℕ} (hmu : 0 < mu n)
    (hj : j ≤ terminalDepth n) :
    Real.log (suffixBoxes n j : ℝ) ≤
      (residualSize n j : ℝ) * Real.log 2 *
        (2 * E - gamma ((actualSwitch n j : ℝ) / residualSize n j)) := by sorry
