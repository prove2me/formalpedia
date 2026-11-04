-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_incidence_dimension_expression_bound
-- name    : ThreeSum.WeightedGlobalPrincipalDimensions.incidence_dimension_expression_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:56:27.519356+00:00
-- url     : https://prove2.me/theorems/f8753174-ed30-4da7-b0ca-9c5deb9d787b
-- title:
--   Weighted Global Principal Dimensions: incidence dimension expression bound
-- statement:
--   The Weighted Global Principal Dimensions construction uses the incidence dimension expression bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrincipalDimensions.lean#L187-L203
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrincipalDimensions.lean#L187-L203

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryPrincipalDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrincipalDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalDimensionBounds
open WeightedGlobalCoverScale WeightedGlobalLocalParameters WeightedGlobalFiniteLedger

theorem ThreeSum.WeightedGlobalPrincipalDimensions.incidence_dimension_expression_bound {m n j : ℕ} (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) (hs : primeRate m < outputRate m) :
    (n : ℝ)*((outputSize m : ℝ)/prime m)^j ≤
      Real.exp (incidenceSlope m)*(n : ℝ)^incidenceCharge m := by sorry
