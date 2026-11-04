-- Prove2me | Theorems.Thm_ThreeSum_BinomialEntropy_weight_positive
-- name    : ThreeSum.BinomialEntropy.weight_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:18.663852+00:00
-- url     : https://prove2.me/theorems/f6abe093-203e-4838-867e-c1648a584595
-- title:
--   Binomial Entropy: weight positive
-- statement:
--   The Binomial Entropy construction uses the weight positive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L119-L124
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L119-L124

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

theorem ThreeSum.BinomialEntropy.weight_positive {n k : ℕ} (hk0 : 0 < k) (hk : k < n) :
    0 < weight n k k := by sorry
