-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalRadixOverhead_polynomial_dimension_budget
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalRadixOverhead.polynomial_dimension_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:09:40.655887+00:00
-- url     : https://prove2.me/theorems/5f8ddae1-999d-4b25-a714-3fec34364ad2
-- title:
--   polynomial_dimension_budget
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryRadixOverhead.lean#L52-L65
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryRadixOverhead.lean#L52-L65

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPrincipalDimensions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryRadixOverhead
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalRadixOverhead
open Filter Real Asymptotics WeightedGlobalCoverScale WeightedGlobalPrincipalDimensions
open scoped Topology

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalRadixOverhead.polynomial_dimension_budget {m : ℕ} (hm : 0 < m) (A K e q : ℝ)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (he : e < q) (d : ℕ) (X : ℕ → ℝ)
    (hX : ∀ n : ℕ, 1 < n → X n ≤ K*(n : ℝ)^e) :
    ∀ᶠ n : ℕ in atTop,
      A*((radixLength m n : ℝ)+1)^d*X n ≤ (n : ℝ)^q := by sorry
