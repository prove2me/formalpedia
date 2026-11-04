-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalParameters_numerator_bounds
-- name    : ThreeSum.WeightedGlobalParameters.numerator_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:21:36.504726+00:00
-- url     : https://prove2.me/theorems/90f694e9-d790-4cf1-bb10-51f191d83f58
-- title:
--   Weighted Global Parameters: numerator bounds
-- statement:
--   The Weighted Global Parameters construction uses the numerator bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L201-L213
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalParameters.lean#L201-L213

import Definitions.Def_Submission_Weighted_Parameters
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_Weighted_GlobalParameters
import Theorems.Thm_WeightedCacheParameters_numerator_bounds

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem ThreeSum.WeightedGlobalParameters.numerator_bounds :
    2*WeightedCacheParameters.Bn<certificateExponent*WeightedCacheParameters.Hn ∧
    2*WeightedCacheParameters.Hn-WeightedCacheParameters.Gn+2*WeightedCacheParameters.Qn<certificateExponent*WeightedCacheParameters.Hn ∧
    2*WeightedCacheParameters.An<certificateExponent*WeightedCacheParameters.Hn ∧
    WeightedCacheParameters.Hn+WeightedCacheParameters.Gn<certificateExponent*WeightedCacheParameters.Hn ∧
    2*WeightedCacheParameters.Hn-WeightedCacheParameters.Gn<certificateExponent*WeightedCacheParameters.Hn := by sorry
