-- Prove2me | Theorems.Thm_ThreeSum_TernaryPrincipalDimensions_actual_endpoint_prefix_bound
-- name    : ThreeSum.TernaryPrincipalDimensions.actual_endpoint_prefix_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:56:40.750464+00:00
-- url     : https://prove2.me/theorems/9c469a98-28d8-4ee1-9077-584ed83c595d
-- title:
--   Ternary Principal Dimensions: actual endpoint prefix bound
-- statement:
--   The Ternary Principal Dimensions construction uses the actual endpoint prefix bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPrincipalDimensions.lean#L91-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPrincipalDimensions.lean#L91-L100

import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Definitions.Def_Submission_ThreeSum_TernaryPrincipalDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPrincipalDimensions
open Real TernaryParameters TernaryEntropyRates TernaryDimensionBounds
open TernaryCoverScale TernaryLocalParameters TernaryFiniteLedger

theorem ThreeSum.TernaryPrincipalDimensions.actual_endpoint_prefix_bound {m n j : ℕ} (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) :
    (endpointSize m : ℝ)^j ≤ (endpointSize m : ℝ)*(n : ℝ)^endpointCharge m := by sorry
