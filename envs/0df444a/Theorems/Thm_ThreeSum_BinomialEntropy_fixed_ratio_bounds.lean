-- Prove2me | Theorems.Thm_ThreeSum_BinomialEntropy_fixed_ratio_bounds
-- name    : ThreeSum.BinomialEntropy.fixed_ratio_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:10:45.746198+00:00
-- url     : https://prove2.me/theorems/023c720b-13ac-42c2-9dc2-b88f5f740fc1
-- title:
--   Binomial Entropy: fixed ratio bounds
-- statement:
--   Exact finite error on an integer multiple of a rational-proportion layer.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L186-L207
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L186-L207

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

theorem ThreeSum.BinomialEntropy.fixed_ratio_bounds {c r m : ℕ} (hc : 0 < c) (hr : r ≤ c) (hm : 0 < m) :
    (c : ℝ) * Real.binEntropy ((r : ℝ) / c) - Real.log (c * m + 1 : ℝ) / m ≤
        Real.log ((c * m).choose (r * m) : ℝ) / m ∧
      Real.log ((c * m).choose (r * m) : ℝ) / m ≤
        (c : ℝ) * Real.binEntropy ((r : ℝ) / c) := by sorry
