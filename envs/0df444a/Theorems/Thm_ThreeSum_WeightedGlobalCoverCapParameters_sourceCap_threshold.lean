-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverCapParameters_sourceCap_threshold
-- name    : ThreeSum.WeightedGlobalCoverCapParameters.sourceCap_threshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:00:57.252736+00:00
-- url     : https://prove2.me/theorems/7da3c40e-9982-4b95-8ae9-04d3abfdc504
-- title:
--   Weighted Global Cover Cap Parameters: source Cap threshold
-- statement:
--   The Weighted Global Cover Cap Parameters construction uses the source Cap threshold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverCapParameters.lean#L81-L85
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverCapParameters.lean#L81-L85

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalCoverCapParameters
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps WeightedGlobalCoverFrequency WeightedGlobalPartitionCount TernaryTypeLowerBound

theorem ThreeSum.WeightedGlobalCoverCapParameters.sourceCap_threshold (m p : ℕ) (hp : 0 < p) :
    8*(p+(fieldVertices (fixedLength m) p (fixedAlpha m)).card) ≤ sourceCap m p*p := by sorry
