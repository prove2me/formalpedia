-- Prove2me | Theorems.Thm_ThreeSum_TernaryRadixOverhead_polynomial_radix_budget
-- name    : ThreeSum.TernaryRadixOverhead.polynomial_radix_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:00:21.736576+00:00
-- url     : https://prove2.me/theorems/b34f9c2e-5e1c-4791-a8fb-9e6937bf8b6f
-- title:
--   Ternary Radix Overhead: polynomial radix budget
-- statement:
--   The Ternary Radix Overhead construction uses the polynomial radix budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryRadixOverhead.lean#L10-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryRadixOverhead.lean#L10-L40

import Definitions.Def_Submission_ThreeSum_TernaryPrincipalDimensions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSum_TernaryRadixOverhead
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryRadixOverhead
open Filter Real Asymptotics TernaryCoverScale TernaryPrincipalDimensions
open scoped Topology

theorem ThreeSum.TernaryRadixOverhead.polynomial_radix_budget {m : ℕ} (hm : 0 < m) (A : ℝ) (hA : 0 ≤ A)
    (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      A*((radixLength m n : ℝ)+1)^d ≤ (n : ℝ)^ε := by sorry
