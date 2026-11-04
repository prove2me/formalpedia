-- Prove2me | Theorems.Thm_ThreeSum_BinomialEntropy_weight_bounds
-- name    : ThreeSum.BinomialEntropy.weight_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:03:22.244462+00:00
-- url     : https://prove2.me/theorems/4166de69-48f0-4c3a-afc5-b1356cea1ad6
-- title:
--   Binomial Entropy: weight bounds
-- statement:
--   The Binomial Entropy construction uses the weight bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L108-L117
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L108-L117

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

theorem ThreeSum.BinomialEntropy.weight_bounds {n k : ℕ} (hk : k < n) :
    weight n k k ≤ (n : ℝ) ^ n ∧
      (n : ℝ) ^ n ≤ (n + 1 : ℝ) * weight n k k := by sorry
