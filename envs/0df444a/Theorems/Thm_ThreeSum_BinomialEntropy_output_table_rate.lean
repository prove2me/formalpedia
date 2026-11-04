-- Prove2me | Theorems.Thm_ThreeSum_BinomialEntropy_output_table_rate
-- name    : ThreeSum.BinomialEntropy.output_table_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:53.656149+00:00
-- url     : https://prove2.me/theorems/58a6c2fe-4aab-46db-bc66-3f1eb54fac46
-- title:
--   Binomial Entropy: output table rate
-- statement:
--   The actual local output count has exponent `2 E` relative to `D=2^mu`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L249-L253
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L249-L253

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

theorem ThreeSum.BinomialEntropy.output_table_rate :
    Tendsto (fun m : ℕ => Real.log ((256 * m).choose m : ℝ) / ((m : ℝ) * Real.log 2))
      atTop (𝓝 (2 * ThreeSum.Parameters.E)) := by sorry
