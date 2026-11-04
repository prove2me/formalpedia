-- Prove2me | Theorems.Thm_ThreeSum_Scales_microSize_inv_tendsto_zero
-- name    : ThreeSum.Scales.microSize_inv_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:50.331162+00:00
-- url     : https://prove2.me/theorems/1c40dd0f-a715-44b0-ab18-3bdb0adfa286
-- title:
--   Scales: micro Size inv tendsto zero
-- statement:
--   The Scales construction uses the micro Size inv tendsto zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L120-L122
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L120-L122

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

theorem ThreeSum.Scales.microSize_inv_tendsto_zero :
    Tendsto (fun m : ℕ => (microSize m : ℝ)⁻¹) atTop (𝓝 0) := by sorry
