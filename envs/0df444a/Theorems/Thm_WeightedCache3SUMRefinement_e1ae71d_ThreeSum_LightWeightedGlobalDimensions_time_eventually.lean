-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalDimensions_time_eventually
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalDimensions.time_eventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:43:00.866246+00:00
-- url     : https://prove2.me/theorems/5f4bb6df-9a0a-4d91-b977-f628e4bcd8bd
-- title:
--   time_eventually
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryDimensionsTime.lean#L31-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryDimensionsTime.lean#L31-L42

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryDimensionsTime
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalDimensions
open WeightedGlobalSignedPadding TernaryExtensionEncoding WeightedGlobalCoverScale Filter Real
set_option maxHeartbeats 2000000
variable {p : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalDimensions.time_eventually {m b : ℕ} (hm : 0 < m) (hb : 1 < b)
    {κ ε : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) (K : ℕ) (U : ℕ → ℕ)
    (hU : ∀ n, 1 < n → (U n : ℝ) ≤ (n : ℝ)^κ) :
    ∀ᶠ n : ℕ in atTop, (time (outputSize m) b p K n (U n) : ℝ) ≤ (n : ℝ)^ε := by sorry
