-- Prove2me | Theorems.Thm_ThreeSum_BinomialEntropy_weight_recurrence
-- name    : ThreeSum.BinomialEntropy.weight_recurrence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:10:40.570475+00:00
-- url     : https://prove2.me/theorems/247df15b-c94f-45a5-8223-3a8bcfd5a5c2
-- title:
--   Binomial Entropy: weight recurrence
-- statement:
--   The Binomial Entropy construction uses the weight recurrence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L29-L45
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L29-L45

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

theorem ThreeSum.BinomialEntropy.weight_recurrence {n k j : ℕ} (hj : j < n) :
    weight n k (j + 1) * ((j + 1 : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) =
      weight n k j * ((n - j : ℕ) : ℝ) * (k : ℝ) := by sorry
