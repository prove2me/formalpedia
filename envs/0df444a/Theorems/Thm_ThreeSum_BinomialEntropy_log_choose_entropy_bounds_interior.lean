-- Prove2me | Theorems.Thm_ThreeSum_BinomialEntropy_log_choose_entropy_bounds_interior
-- name    : ThreeSum.BinomialEntropy.log_choose_entropy_bounds_interior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:30.612505+00:00
-- url     : https://prove2.me/theorems/85eb5c92-6907-4bd5-8f37-59bf9f889ae6
-- title:
--   Binomial Entropy: log choose entropy bounds interior
-- statement:
--   The Binomial Entropy construction uses the log choose entropy bounds interior property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L152-L164
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L152-L164

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

theorem ThreeSum.BinomialEntropy.log_choose_entropy_bounds_interior {n k : ℕ} (hk0 : 0 < k) (hk : k < n) :
    (n : ℝ) * Real.binEntropy ((k : ℝ) / n) - Real.log (n + 1 : ℝ) ≤
        Real.log (n.choose k : ℝ) ∧
      Real.log (n.choose k : ℝ) ≤ (n : ℝ) * Real.binEntropy ((k : ℝ) / n) := by sorry
