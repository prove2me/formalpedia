-- Prove2me | Theorems.Thm_ThreeSum_TernaryPrincipalDimensions_query_dimension_expression_bound
-- name    : ThreeSum.TernaryPrincipalDimensions.query_dimension_expression_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:56:45.385546+00:00
-- url     : https://prove2.me/theorems/cfee7493-ed1b-4653-bf79-b496183a7a0f
-- title:
--   Ternary Principal Dimensions: query dimension expression bound
-- statement:
--   The literal wanted-volume/query-dimension expression, including its
--   exact +1 boundary factor. A caller must separately prove that an executed
--   enumerator has at most this many wanted copies.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPrincipalDimensions.lean#L143-L177
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPrincipalDimensions.lean#L143-L177

import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Definitions.Def_Submission_ThreeSum_TernaryPrincipalDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPrincipalDimensions
open Real TernaryParameters TernaryEntropyRates TernaryDimensionBounds
open TernaryCoverScale TernaryLocalParameters TernaryFiniteLedger

theorem ThreeSum.TernaryPrincipalDimensions.query_dimension_expression_bound {m n j : ℕ} (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) (hs : primeRate m < outputRate m)
    (Q : TernaryJointType.TritWord (fixedLength (j*m)))
    (hQ : TernaryJointType.HasType Q (fixedPi (j*m))) :
    (n : ℝ)*((outputSize m : ℝ)/prime m)^j*
      (TernaryBank.nearWords Q (queryDeficit m j)).card ≤
      (Real.exp (querySlope m)/z)*(n : ℝ)^queryCharge m := by sorry
