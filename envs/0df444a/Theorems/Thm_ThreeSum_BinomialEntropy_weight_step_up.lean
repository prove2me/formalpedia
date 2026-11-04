-- Prove2me | Theorems.Thm_ThreeSum_BinomialEntropy_weight_step_up
-- name    : ThreeSum.BinomialEntropy.weight_step_up
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:01.191271+00:00
-- url     : https://prove2.me/theorems/45d0b4d0-e412-4c17-81cd-d347a471ee0a
-- title:
--   Binomial Entropy: weight step up
-- statement:
--   The Binomial Entropy construction uses the weight step up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L47-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L47-L60

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

theorem ThreeSum.BinomialEntropy.weight_step_up {n k j : ℕ} (hk : k < n) (hj : j < k) :
    weight n k j ≤ weight n k (j + 1) := by sorry
