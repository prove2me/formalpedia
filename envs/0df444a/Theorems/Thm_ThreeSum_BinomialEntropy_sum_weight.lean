-- Prove2me | Theorems.Thm_ThreeSum_BinomialEntropy_sum_weight
-- name    : ThreeSum.BinomialEntropy.sum_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:20.687192+00:00
-- url     : https://prove2.me/theorems/8b7a46a6-f8d2-421d-9da0-9657491f5af8
-- title:
--   Binomial Entropy: sum weight
-- statement:
--   The Binomial Entropy construction uses the sum weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L98-L106
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L98-L106

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

theorem ThreeSum.BinomialEntropy.sum_weight {n k : ℕ} (hk : k ≤ n) :
    ∑ j ∈ range (n + 1), weight n k j = (n : ℝ) ^ n := by sorry
