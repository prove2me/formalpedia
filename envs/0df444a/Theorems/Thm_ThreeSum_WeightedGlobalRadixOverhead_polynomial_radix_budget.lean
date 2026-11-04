-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalRadixOverhead_polynomial_radix_budget
-- name    : ThreeSum.WeightedGlobalRadixOverhead.polynomial_radix_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:59:19.844953+00:00
-- url     : https://prove2.me/theorems/5a445b46-2130-4942-ad15-60088cbc4ee4
-- title:
--   Weighted Global Radix Overhead: polynomial radix budget
-- statement:
--   The Weighted Global Radix Overhead construction uses the polynomial radix budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryRadixOverhead.lean#L17-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryRadixOverhead.lean#L17-L47

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryPrincipalDimensions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalRadixOverhead
open Filter Real Asymptotics WeightedGlobalCoverScale WeightedGlobalPrincipalDimensions
open scoped Topology

theorem ThreeSum.WeightedGlobalRadixOverhead.polynomial_radix_budget {m : ℕ} (hm : 0 < m) (A : ℝ) (hA : 0 ≤ A)
    (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      A*((radixLength m n : ℝ)+1)^d ≤ (n : ℝ)^ε := by sorry
