-- Prove2me | Theorems.Thm_ThreeSum_Scales_localThreshold_log_formula
-- name    : ThreeSum.Scales.localThreshold_log_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:35:31.64385+00:00
-- url     : https://prove2.me/theorems/da08ebc8-043c-47d5-87fa-62414f0e1619
-- title:
--   Scales: local Threshold log formula
-- statement:
--   The Scales construction uses the local Threshold log formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L457-L465
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L457-L465

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

theorem ThreeSum.Scales.localThreshold_log_formula (h : ℕ) :
    Real.log (LocalCoverBounds.localThreshold h : ℝ) =
      Real.log (LocalCoverBounds.outputCount (512 * h) h : ℝ) +
        (2 * h : ℝ) * Real.log 2 := by sorry
