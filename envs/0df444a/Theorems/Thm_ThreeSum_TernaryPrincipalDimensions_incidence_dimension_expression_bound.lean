-- Prove2me | Theorems.Thm_ThreeSum_TernaryPrincipalDimensions_incidence_dimension_expression_bound
-- name    : ThreeSum.TernaryPrincipalDimensions.incidence_dimension_expression_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:56:43.330862+00:00
-- url     : https://prove2.me/theorems/f9ee86d6-811b-44d9-b9e3-00275dd6377b
-- title:
--   Ternary Principal Dimensions: incidence dimension expression bound
-- statement:
--   The Ternary Principal Dimensions construction uses the incidence dimension expression bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPrincipalDimensions.lean#L179-L195
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPrincipalDimensions.lean#L179-L195

import Definitions.Def_Submission_ThreeSum_TernaryFiniteLedger
import Definitions.Def_Submission_ThreeSum_TernaryPrincipalDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPrincipalDimensions
open Real TernaryParameters TernaryEntropyRates TernaryDimensionBounds
open TernaryCoverScale TernaryLocalParameters TernaryFiniteLedger

theorem ThreeSum.TernaryPrincipalDimensions.incidence_dimension_expression_bound {m n j : ℕ} (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) (hs : primeRate m < outputRate m) :
    (n : ℝ)*((outputSize m : ℝ)/prime m)^j ≤
      Real.exp (incidenceSlope m)*(n : ℝ)^incidenceCharge m := by sorry
