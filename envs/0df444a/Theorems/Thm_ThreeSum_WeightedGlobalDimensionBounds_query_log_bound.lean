-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalDimensionBounds_query_log_bound
-- name    : ThreeSum.WeightedGlobalDimensionBounds.query_log_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:48:51.362404+00:00
-- url     : https://prove2.me/theorems/8e7fa13f-432f-4ced-a248-897a2272ac5f
-- title:
--   Weighted Global Dimension Bounds: query log bound
-- statement:
--   The Weighted Global Dimension Bounds construction uses the query log bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/DimensionBounds.lean#L68-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/DimensionBounds.lean#L68-L85

import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_QueryBudget
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalDimensionBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalBank WeightedGlobalParameters

theorem ThreeSum.WeightedGlobalDimensionBounds.query_log_bound {m j : ℕ} (Q : TritWord (fixedLength (j*m)))
    (hQ : HasType Q (fixedPi (j*m))) :
    Real.log ((nearWords Q (queryDeficit m j)).card : ℝ)≤
      (fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy-1024*Real.log z := by sorry
