-- Prove2me | Theorems.Thm_ThreeSum_BinomialEntropy_entropy_numerator
-- name    : ThreeSum.BinomialEntropy.entropy_numerator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:22.711204+00:00
-- url     : https://prove2.me/theorems/a0783244-79ee-444e-b318-50bd2ce7a5ad
-- title:
--   Binomial Entropy: entropy numerator
-- statement:
--   The Binomial Entropy construction uses the entropy numerator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L135-L150
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L135-L150

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

theorem ThreeSum.BinomialEntropy.entropy_numerator {n k : ℕ} (hk0 : 0 < k) (hk : k < n) :
    (n : ℝ) * Real.binEntropy ((k : ℝ) / n) = (n : ℝ) * Real.log n -
      (k : ℝ) * Real.log k - ((n - k : ℕ) : ℝ) * Real.log (n - k : ℕ) := by sorry
