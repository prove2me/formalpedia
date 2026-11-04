-- Prove2me | Theorems.Thm_ThreeSum_BinomialEntropy_weight_mode
-- name    : ThreeSum.BinomialEntropy.weight_mode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:18.715196+00:00
-- url     : https://prove2.me/theorems/a9a51d67-6bc0-4df9-b2bc-8133a6d95a35
-- title:
--   Binomial Entropy: weight mode
-- statement:
--   The Binomial Entropy construction uses the weight mode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L83-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L83-L96

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

theorem ThreeSum.BinomialEntropy.weight_mode {n k j : ℕ} (hk : k < n) : weight n k j ≤ weight n k k := by sorry
