-- Prove2me | Theorems.Thm_ThreeSum_Scales_localPrime_log_interval
-- name    : ThreeSum.Scales.localPrime_log_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:35:31.952403+00:00
-- url     : https://prove2.me/theorems/56af8518-ef25-46db-a29c-16f41f9c154b
-- title:
--   Scales: local Prime log interval
-- statement:
--   The Scales construction uses the local Prime log interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L477-L495
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L477-L495

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Sqrt
import Definitions.Def_Submission_ThreeSum_Scales
set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology
noncomputable section

theorem ThreeSum.Scales.localPrime_log_interval (h : ℕ) :
    Real.log (LocalCoverBounds.localThreshold h : ℝ) ≤
      2 * Real.log (LocalCoverBounds.localPrime h : ℝ) ∧
    2 * Real.log (LocalCoverBounds.localPrime h : ℝ) ≤
      Real.log 16 + Real.log (LocalCoverBounds.localThreshold h : ℝ) := by sorry
