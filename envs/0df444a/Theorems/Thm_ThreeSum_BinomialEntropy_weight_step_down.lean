-- Prove2me | Theorems.Thm_ThreeSum_BinomialEntropy_weight_step_down
-- name    : ThreeSum.BinomialEntropy.weight_step_down
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:17.381956+00:00
-- url     : https://prove2.me/theorems/31d6364b-cf2e-4503-81d6-aa986f028c18
-- title:
--   Binomial Entropy: weight step down
-- statement:
--   The Binomial Entropy construction uses the weight step down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L62-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L62-L81

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

theorem ThreeSum.BinomialEntropy.weight_step_down {n k j : ℕ} (hk : k < n) (hj : k ≤ j) :
    weight n k (j + 1) ≤ weight n k j := by sorry
