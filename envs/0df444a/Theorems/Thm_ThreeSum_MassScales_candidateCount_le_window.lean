-- Prove2me | Theorems.Thm_ThreeSum_MassScales_candidateCount_le_window
-- name    : ThreeSum.MassScales.candidateCount_le_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:40:00.757181+00:00
-- url     : https://prove2.me/theorems/30dd1cb7-fdef-4daf-8677-e6f1d14d1a32
-- title:
--   Mass Scales: candidate Count le window
-- statement:
--   The Mass Scales construction uses the candidate Count le window property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MassScales.lean#L100-L106
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/MassScales.lean#L100-L106

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

theorem ThreeSum.MassScales.candidateCount_le_window (n : ℕ) : candidateCount n ≤ 4 * primeWindow n := by sorry
