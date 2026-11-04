-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalParameters_Hpi_bounds
-- name    : ThreeSum.WeightedGlobalParameters.Hpi_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:03:04.006015+00:00
-- url     : https://prove2.me/theorems/91f45cf7-b2c4-40e6-a4da-5c055658e77b
-- title:
--   Weighted Global Parameters: Hpi bounds
-- statement:
--   The Weighted Global Parameters construction uses the Hpi bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L45-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L45-L52

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ThreeSum.WeightedGlobalParameters.Hpi_bounds : (81443/100000 : ℝ)≤Hpi ∧ Hpi≤(81444/100000 : ℝ) := by sorry
