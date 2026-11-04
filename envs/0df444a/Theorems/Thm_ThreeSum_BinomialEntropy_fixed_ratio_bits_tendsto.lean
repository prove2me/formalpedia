-- Prove2me | Theorems.Thm_ThreeSum_BinomialEntropy_fixed_ratio_bits_tendsto
-- name    : ThreeSum.BinomialEntropy.fixed_ratio_bits_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:02:44.735982+00:00
-- url     : https://prove2.me/theorems/0f7d12da-abbe-4a02-910e-2d59b01bd835
-- title:
--   Binomial Entropy: fixed ratio bits tendsto
-- statement:
--   The Binomial Entropy construction uses the fixed ratio bits tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L242-L246
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L242-L246

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

theorem ThreeSum.BinomialEntropy.fixed_ratio_bits_tendsto {c r : ℕ} (hc : 0 < c) (hr : r ≤ c) :
    Tendsto (fun m : ℕ => Real.log ((c * m).choose (r * m) : ℝ) / ((m : ℝ) * Real.log 2))
      atTop (𝓝 ((c : ℝ) * ThreeSum.Parameters.entropy ((r : ℝ) / c))) := by sorry
