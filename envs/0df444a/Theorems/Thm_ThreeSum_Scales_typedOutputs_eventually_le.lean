-- Prove2me | Theorems.Thm_ThreeSum_Scales_typedOutputs_eventually_le
-- name    : ThreeSum.Scales.typedOutputs_eventually_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:52:39.953209+00:00
-- url     : https://prove2.me/theorems/d0ad90cb-e471-4bc1-b3e6-afb4d605a591
-- title:
--   Scales: typed Outputs eventually le
-- statement:
--   The Scales construction uses the typed Outputs eventually le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L329-L331
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L329-L331

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

theorem ThreeSum.Scales.typedOutputs_eventually_le {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (typedOutputs n : ℝ) ≤ (n : ℝ) ^ (2 * Parameters.E / 5 + d) := by sorry
