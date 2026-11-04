-- Prove2me | Theorems.Thm_ThreeSum_Scales_microSize_real_root_bounds
-- name    : ThreeSum.Scales.microSize_real_root_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:34:47.731005+00:00
-- url     : https://prove2.me/theorems/56dfbe33-a749-4a37-a901-82a2c158e108
-- title:
--   Scales: micro Size real root bounds
-- statement:
--   The Scales construction uses the micro Size real root bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L230-L243
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L230-L243

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

theorem ThreeSum.Scales.microSize_real_root_bounds (m : ℕ) :
    (microSize m : ℝ) ≤ (m : ℝ) ^ (1 / 3 : ℝ) ∧
      (m : ℝ) ^ (1 / 3 : ℝ) < (microSize m : ℝ) + 3 := by sorry
