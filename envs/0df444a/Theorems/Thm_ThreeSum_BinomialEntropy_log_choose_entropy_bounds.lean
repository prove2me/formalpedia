-- Prove2me | Theorems.Thm_ThreeSum_BinomialEntropy_log_choose_entropy_bounds
-- name    : ThreeSum.BinomialEntropy.log_choose_entropy_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:59:44.772266+00:00
-- url     : https://prove2.me/theorems/9badbdf0-7944-49b2-b803-68d5f83db0ca
-- title:
--   Binomial Entropy: log choose entropy bounds
-- statement:
--   Finite entropy bounds, including zero and full layers.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L167-L183
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L167-L183

import Definitions.Def_Submission_ThreeSum_Parameters
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Monotone.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.BinomialEntropy
open Finset Real Set Filter
open scoped Topology
set_option maxRecDepth 10000

theorem ThreeSum.BinomialEntropy.log_choose_entropy_bounds {n k : ℕ} (hk : k ≤ n) :
    (n : ℝ) * Real.binEntropy ((k : ℝ) / n) - Real.log (n + 1 : ℝ) ≤
        Real.log (n.choose k : ℝ) ∧
      Real.log (n.choose k : ℝ) ≤ (n : ℝ) * Real.binEntropy ((k : ℝ) / n) := by sorry
