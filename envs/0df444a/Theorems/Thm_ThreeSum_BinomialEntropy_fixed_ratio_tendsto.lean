-- Prove2me | Theorems.Thm_ThreeSum_BinomialEntropy_fixed_ratio_tendsto
-- name    : ThreeSum.BinomialEntropy.fixed_ratio_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:32.636604+00:00
-- url     : https://prove2.me/theorems/9222d212-fd7a-477f-bc83-adcac34d286a
-- title:
--   Binomial Entropy: fixed ratio tendsto
-- statement:
--   The entropy rate follows from the explicit logarithmic finite error.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L227-L240
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L227-L240

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

theorem ThreeSum.BinomialEntropy.fixed_ratio_tendsto {c r : ℕ} (hc : 0 < c) (hr : r ≤ c) :
    Tendsto (fun m : ℕ => Real.log ((c * m).choose (r * m) : ℝ) / m) atTop
      (𝓝 ((c : ℝ) * Real.binEntropy ((r : ℝ) / c))) := by sorry
