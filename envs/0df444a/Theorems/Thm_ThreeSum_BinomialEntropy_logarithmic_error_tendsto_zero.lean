-- Prove2me | Theorems.Thm_ThreeSum_BinomialEntropy_logarithmic_error_tendsto_zero
-- name    : ThreeSum.BinomialEntropy.logarithmic_error_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:59:34.631233+00:00
-- url     : https://prove2.me/theorems/62aeeb06-7009-4bb9-b560-0f47df860fd2
-- title:
--   Binomial Entropy: logarithmic error tendsto zero
-- statement:
--   The Binomial Entropy construction uses the logarithmic error tendsto zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L209-L224
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L209-L224

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

theorem ThreeSum.BinomialEntropy.logarithmic_error_tendsto_zero {c : ℕ} (hc : 0 < c) :
    Tendsto (fun m : ℕ => Real.log (c * m + 1 : ℝ) / m) atTop (𝓝 0) := by sorry
