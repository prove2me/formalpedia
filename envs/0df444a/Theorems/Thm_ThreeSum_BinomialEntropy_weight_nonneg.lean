-- Prove2me | Theorems.Thm_ThreeSum_BinomialEntropy_weight_nonneg
-- name    : ThreeSum.BinomialEntropy.weight_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:52.876876+00:00
-- url     : https://prove2.me/theorems/be8ab8bd-36b5-4d7c-9ddb-f76668a74d8b
-- title:
--   Binomial Entropy: weight nonneg
-- statement:
--   The Binomial Entropy construction uses the weight nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L25-L27
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L25-L27

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

theorem ThreeSum.BinomialEntropy.weight_nonneg (n k j : ℕ) : 0 ≤ weight n k j := by sorry
