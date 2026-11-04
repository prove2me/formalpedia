-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalDimensionBounds_query_boundary
-- name    : ThreeSum.WeightedGlobalDimensionBounds.query_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:48:58.507666+00:00
-- url     : https://prove2.me/theorems/816b920f-1851-4c14-804f-bae806ea3b5f
-- title:
--   Weighted Global Dimension Bounds: query boundary
-- statement:
--   The Weighted Global Dimension Bounds construction uses the query boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/DimensionBounds.lean#L39-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/DimensionBounds.lean#L39-L42

import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_QueryBudget
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Theorems.Thm_ThreeSum_WeightedSchedule_query_boundary

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalDimensionBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalBank WeightedGlobalParameters

theorem ThreeSum.WeightedGlobalDimensionBounds.query_boundary {m j : ℕ} {Q : TritWord (fixedLength (j*m))}
    (hQ : HasType Q (fixedPi (j*m))) : cacheCost Q+1024-bankCut m j=queryDeficit m j := by sorry
