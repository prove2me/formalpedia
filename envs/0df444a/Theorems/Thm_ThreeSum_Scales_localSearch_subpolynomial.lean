-- Prove2me | Theorems.Thm_ThreeSum_Scales_localSearch_subpolynomial
-- name    : ThreeSum.Scales.localSearch_subpolynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:06:03.284429+00:00
-- url     : https://prove2.me/theorems/42515306-1a06-4983-812e-64d998bcd100
-- title:
--   Scales: local Search subpolynomial
-- statement:
--   The Scales construction uses the local Search subpolynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L321-L323
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L321-L323

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

theorem ThreeSum.Scales.localSearch_subpolynomial (C : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (localSearch C n : ℝ) ≤ (n : ℝ) ^ d := by sorry
