-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalDimensionBounds_endpoint_in_bank
-- name    : ThreeSum.WeightedGlobalDimensionBounds.endpoint_in_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:48:44.681164+00:00
-- url     : https://prove2.me/theorems/ca431c28-d376-440a-9bab-1274b035f839
-- title:
--   Weighted Global Dimension Bounds: endpoint in bank
-- statement:
--   The Weighted Global Dimension Bounds construction uses the endpoint in bank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/DimensionBounds.lean#L44-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/DimensionBounds.lean#L44-L49

import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_QueryBudget
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalDimensionBounds
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalBank WeightedGlobalParameters

theorem ThreeSum.WeightedGlobalDimensionBounds.endpoint_in_bank {m j : ℕ} {A : TritWord (fixedLength (j*m))}
    (hA : HasType A (fixedAlpha (j*m))) : A∈bank (fixedLength (j*m)) (bankCut m j) := by sorry
