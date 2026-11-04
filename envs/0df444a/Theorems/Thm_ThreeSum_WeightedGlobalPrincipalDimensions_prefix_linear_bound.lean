-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPrincipalDimensions_prefix_linear_bound
-- name    : ThreeSum.WeightedGlobalPrincipalDimensions.prefix_linear_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:55:40.923205+00:00
-- url     : https://prove2.me/theorems/0d092d65-8934-4f5b-9d87-39b16add3e25
-- title:
--   Weighted Global Principal Dimensions: prefix linear bound
-- statement:
--   The Weighted Global Principal Dimensions construction uses the prefix linear bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrincipalDimensions.lean#L27-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPrincipalDimensions.lean#L27-L47

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_Submission_Weighted_Global_TernaryPrincipalDimensions
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPrincipalDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalDimensionBounds
open WeightedGlobalCoverScale WeightedGlobalLocalParameters WeightedGlobalFiniteLedger

theorem ThreeSum.WeightedGlobalPrincipalDimensions.prefix_linear_bound {M n j : ℕ} (hM : 1 < M) (hn : 1 < n)
    (hj : j ≤ Nat.clog M (n^2)) {a : ℝ} (ha : 0 ≤ a) :
    (j : ℝ)*a ≤ a+(2*a/Real.log M)*Real.log n := by sorry
