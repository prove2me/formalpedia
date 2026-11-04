-- Prove2me | Theorems.Thm_ThreeSum_Scales_scoreBase_log_over_primeBase_tendsto_zero
-- name    : ThreeSum.Scales.scoreBase_log_over_primeBase_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:36:51.176739+00:00
-- url     : https://prove2.me/theorems/b4b71a86-3d41-410c-b7c9-d9907c7c9e54
-- title:
--   Scales: score Base log over prime Base tendsto zero
-- statement:
--   The Scales construction uses the score Base log over prime Base tendsto zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L792-L804
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L792-L804

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

theorem ThreeSum.Scales.scoreBase_log_over_primeBase_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log (16 * ((k : ℝ) + 2) * (inputBits n + 1)) /
      Real.log (4 * primeWindow n : ℝ)) atTop (𝓝 0) := by sorry
