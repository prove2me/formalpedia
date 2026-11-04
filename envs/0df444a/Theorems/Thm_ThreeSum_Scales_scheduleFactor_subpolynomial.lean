-- Prove2me | Theorems.Thm_ThreeSum_Scales_scheduleFactor_subpolynomial
-- name    : ThreeSum.Scales.scheduleFactor_subpolynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:52:37.654271+00:00
-- url     : https://prove2.me/theorems/917b9718-cbea-4d1d-9138-3cd1c1138dea
-- title:
--   Scales: schedule Factor subpolynomial
-- statement:
--   The Scales construction uses the schedule Factor subpolynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L325-L327
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L325-L327

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

theorem ThreeSum.Scales.scheduleFactor_subpolynomial (C : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (scheduleFactor C n : ℝ) ≤ (n : ℝ) ^ d := by sorry
