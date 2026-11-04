-- Prove2me | Theorems.Thm_ThreeSum_MassScales_nat_log_rate_pow
-- name    : ThreeSum.MassScales.nat_log_rate_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:11:48.986345+00:00
-- url     : https://prove2.me/theorems/e0a1e2a2-d0ac-486f-b271-854ca9e33510
-- title:
--   Mass Scales: nat log rate pow
-- statement:
--   The Mass Scales construction uses the nat log rate pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MassScales.lean#L95-L98
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MassScales.lean#L95-L98

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

theorem ThreeSum.MassScales.nat_log_rate_pow {f : ℕ → ℕ} {a : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a)) (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log ((f n ^ k : ℕ) : ℝ) / Real.log n) atTop (𝓝 ((k : ℝ) * a)) := by sorry
