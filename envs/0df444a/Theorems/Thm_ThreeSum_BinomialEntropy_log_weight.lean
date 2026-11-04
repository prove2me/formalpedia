-- Prove2me | Theorems.Thm_ThreeSum_BinomialEntropy_log_weight
-- name    : ThreeSum.BinomialEntropy.log_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:21.30445+00:00
-- url     : https://prove2.me/theorems/06aa02f0-c438-4943-8e9a-1f5697c4c480
-- title:
--   Binomial Entropy: log weight
-- statement:
--   The Binomial Entropy construction uses the log weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L126-L133
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L126-L133

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

theorem ThreeSum.BinomialEntropy.log_weight {n k : ℕ} (hk0 : 0 < k) (hk : k < n) :
    Real.log (weight n k k) = Real.log (n.choose k : ℝ) +
      (k : ℝ) * Real.log k + ((n - k : ℕ) : ℝ) * Real.log (n - k : ℕ) := by sorry
