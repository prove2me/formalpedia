-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPrincipalDimensions_prefix_dimension_bound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrincipalDimensions.prefix_dimension_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:07:15.252799+00:00
-- url     : https://prove2.me/theorems/d9b139a6-baae-4ffa-bb71-366a13eac2ae
-- title:
--   prefix_dimension_bound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrincipalDimensions.lean#L49-L63
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPrincipalDimensions.lean#L49-L63

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryFiniteLedger
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrincipalDimensions
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrincipalDimensions
open Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalDimensionBounds
open WeightedGlobalCoverScale WeightedGlobalLocalParameters WeightedGlobalFiniteLedger

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPrincipalDimensions.prefix_dimension_bound {M n j : ℕ} (hM : 1 < M) (hn : 1 < n)
    (hj : j ≤ Nat.clog M (n^2)) {a X : ℝ} (ha : 0 ≤ a) (hX : 0 ≤ X)
    (hlog : Real.log X ≤ (j : ℝ)*a) :
    X ≤ Real.exp a*(n : ℝ)^(2*a/Real.log M) := by sorry
