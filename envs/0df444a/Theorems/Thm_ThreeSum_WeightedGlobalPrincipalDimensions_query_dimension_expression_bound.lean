-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_query_dimension_expression_bound
-- name    : ThreeSum.WeightedGlobalPrincipalDimensions.query_dimension_expression_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:56:21.9101+00:00
-- url     : https://prove2.me/theorems/943784c4-34fe-456f-9d5c-60814e5cdd45
-- title:
--   Weighted Global Principal Dimensions: query dimension expression bound
-- statement:
--   The literal wanted-volume/query-dimension expression, including its
--   exact +1 boundary factor. A caller must separately prove that an executed
--   enumerator has at most this many wanted copies.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrincipalDimensions.lean#L150-L185
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrincipalDimensions.lean#L150-L185

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryPrincipalDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrincipalDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalDimensionBounds
open WeightedGlobalCoverScale WeightedGlobalLocalParameters WeightedGlobalFiniteLedger

theorem ThreeSum.WeightedGlobalPrincipalDimensions.query_dimension_expression_bound {m n j : ℕ} (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) (hs : primeRate m < outputRate m)
    (Q : TernaryJointType.TritWord (fixedLength (j*m)))
    (hQ : TernaryJointType.HasType Q (fixedPi (j*m))) :
    (n : ℝ)*((outputSize m : ℝ)/prime m)^j*
      (WeightedGlobalBank.nearWords Q (queryDeficit m j)).card ≤
      (Real.exp (querySlope m)/z^1024)*(n : ℝ)^queryCharge m := by sorry
