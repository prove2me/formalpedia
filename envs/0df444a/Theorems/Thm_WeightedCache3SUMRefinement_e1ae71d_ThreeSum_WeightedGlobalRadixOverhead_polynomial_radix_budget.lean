-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalRadixOverhead_polynomial_radix_budget
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalRadixOverhead.polynomial_radix_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:08:16.395289+00:00
-- url     : https://prove2.me/theorems/164e9632-37fc-4357-87fa-18ded999b8cb
-- title:
--   polynomial_radix_budget
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryRadixOverhead.lean#L17-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryRadixOverhead.lean#L17-L47

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalRadixOverhead.polynomial_radix_budget {m : ℕ} (hm : 0 < m) (A : ℝ) (hA : 0 ≤ A)
    (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      A*((radixLength m n : ℝ)+1)^d ≤ (n : ℝ)^ε := by sorry
