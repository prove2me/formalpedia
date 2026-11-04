-- Prove2me | Theorems.Thm_ThreeSum_BinomialEntropy_vertex_table_rate
-- name    : ThreeSum.BinomialEntropy.vertex_table_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:10:47.433197+00:00
-- url     : https://prove2.me/theorems/3db39740-6275-4433-84a5-6b3be73dc50f
-- title:
--   Binomial Entropy: vertex table rate
-- statement:
--   The actual local vertex count, with `mu=2h`, has the multiplicity rate used by the cover.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L256-L266
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BinomialEntropy.lean#L256-L266

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

theorem ThreeSum.BinomialEntropy.vertex_table_rate :
    Tendsto (fun h : ℕ => Real.log ((512 * h).choose h : ℝ) / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 (ThreeSum.Parameters.E + 1 / 2 + ThreeSum.Parameters.kappa / 2)) := by sorry
