-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalParameters_projection_fiber_bits_lt_half_Hpi
-- name    : ThreeSum.WeightedGlobalParameters.projection_fiber_bits_lt_half_Hpi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:57:44.97518+00:00
-- url     : https://prove2.me/theorems/a0471aec-d7e3-4424-90d0-d6256783d1db
-- title:
--   Weighted Global Parameters: projection fiber bits lt half Hpi
-- statement:
--   The Weighted Global Parameters construction uses the projection fiber bits lt half Hpi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L174-L177
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L174-L177

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ThreeSum.WeightedGlobalParameters.projection_fiber_bits_lt_half_Hpi {m : ℕ} (hm : 0 < m) :
    Real.log (((30000000000000 * m).choose (292746547000 * m) : ℕ) : ℝ) /
      ((30000000000000 * m : ℕ) * Real.log 2) < Hpi / 2 := by sorry
