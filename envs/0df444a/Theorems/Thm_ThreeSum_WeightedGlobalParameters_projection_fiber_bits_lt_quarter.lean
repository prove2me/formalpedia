-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalParameters_projection_fiber_bits_lt_quarter
-- name    : ThreeSum.WeightedGlobalParameters.projection_fiber_bits_lt_quarter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:56:13.410264+00:00
-- url     : https://prove2.me/theorems/2f4bdf0b-37c9-46f6-bd8c-112a0dcb4aad
-- title:
--   Weighted Global Parameters: projection fiber bits lt quarter
-- statement:
--   The Weighted Global Parameters construction uses the projection fiber bits lt quarter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L163-L172
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L163-L172

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ThreeSum.WeightedGlobalParameters.projection_fiber_bits_lt_quarter {m : ℕ} (hm : 0 < m) :
    Real.log (((30000000000000 * m).choose (292746547000 * m) : ℕ) : ℝ) /
      ((30000000000000 * m : ℕ) * Real.log 2) < (1 / 4 : ℝ) := by sorry
