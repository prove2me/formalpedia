-- Prove2me | Theorems.Thm_ThreeSum_MassScales_wantedMajorant_eventually_le
-- name    : ThreeSum.MassScales.wantedMajorant_eventually_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:40:51.223649+00:00
-- url     : https://prove2.me/theorems/e282657f-fc06-4f88-8f53-e87a49031341
-- title:
--   Mass Scales: wanted Majorant eventually le
-- statement:
--   The Mass Scales construction uses the wanted Majorant eventually le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MassScales.lean#L202-L204
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MassScales.lean#L202-L204

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

theorem ThreeSum.MassScales.wantedMajorant_eventually_le {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, wantedMajorant n ≤ (n : ℝ) ^ (2 - (1 / 2 + bandShift) / 5 + d) := by sorry
