-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalParameters_Halpha_bounds
-- name    : ThreeSum.WeightedGlobalParameters.Halpha_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:56:03.992191+00:00
-- url     : https://prove2.me/theorems/4a2785d5-20d0-4977-b522-230fee4d517e
-- title:
--   Weighted Global Parameters: Halpha bounds
-- statement:
--   The Weighted Global Parameters construction uses the Halpha bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L55-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L55-L62

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ThreeSum.WeightedGlobalParameters.Halpha_bounds : (51129/100000 : ℝ)≤Halpha ∧ Halpha≤(51130/100000 : ℝ) := by sorry
