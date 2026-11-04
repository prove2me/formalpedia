-- Prove2me | Theorems.Thm_ThreeSum_Scales_scoreLoss_subpolynomial
-- name    : ThreeSum.Scales.scoreLoss_subpolynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:52:57.137356+00:00
-- url     : https://prove2.me/theorems/0d6ce091-71f0-458b-81e6-b2c0eaa28be2
-- title:
--   Scales: score Loss subpolynomial
-- statement:
--   The Scales construction uses the score Loss subpolynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L831-L833
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L831-L833

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

theorem ThreeSum.Scales.scoreLoss_subpolynomial (k : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (scoreLoss k n : ℝ) ≤ (n : ℝ) ^ d := by sorry
