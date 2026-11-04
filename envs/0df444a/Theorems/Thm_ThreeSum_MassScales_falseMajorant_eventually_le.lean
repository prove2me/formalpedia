-- Prove2me | Theorems.Thm_ThreeSum_MassScales_falseMajorant_eventually_le
-- name    : ThreeSum.MassScales.falseMajorant_eventually_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:14:37.222477+00:00
-- url     : https://prove2.me/theorems/9f2149c9-b9d4-4d99-b81f-eb28454ce07d
-- title:
--   Mass Scales: false Majorant eventually le
-- statement:
--   The Mass Scales construction uses the false Majorant eventually le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MassScales.lean#L206-L208
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MassScales.lean#L206-L208

import Definitions.Def_Submission_ThreeSum_HierarchyScales
import Definitions.Def_Submission_ThreeSum_MassScales
set_option autoImplicit false
open ThreeSum ThreeSum.MassScales
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.CostLedger ThreeSum.HierarchyScales
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section

theorem ThreeSum.MassScales.falseMajorant_eventually_le (k : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, falseMajorant k n ≤ (n : ℝ) ^ (2 - (1 / 2 - bandShift) / 5 + d) := by sorry
