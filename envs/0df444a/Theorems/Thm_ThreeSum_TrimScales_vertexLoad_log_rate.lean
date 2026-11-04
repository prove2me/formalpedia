-- Prove2me | Theorems.Thm_ThreeSum_TrimScales_vertexLoad_log_rate
-- name    : ThreeSum.TrimScales.vertexLoad_log_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:13:34.0619+00:00
-- url     : https://prove2.me/theorems/b8e01965-bb2e-4945-bd60-1600638bdd9c
-- title:
--   Trim Scales: vertex Load log rate
-- statement:
--   The Trim Scales construction uses the vertex Load log rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TrimScales.lean#L76-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TrimScales.lean#L76-L90

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section

theorem ThreeSum.TrimScales.vertexLoad_log_rate :
    Tendsto (fun h : ℕ => Real.log (vertexLoad h) / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 (Parameters.kappa / 2)) := by sorry
