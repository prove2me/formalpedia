-- Prove2me | Theorems.Thm_ThreeSum_Scales_primeWindow_subpolynomial
-- name    : ThreeSum.Scales.primeWindow_subpolynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:52:41.745072+00:00
-- url     : https://prove2.me/theorems/974eb4d3-983b-4bf3-9ce6-ae5be17de03c
-- title:
--   Scales: prime Window subpolynomial
-- statement:
--   The Scales construction uses the prime Window subpolynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L388-L390
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L388-L390

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

theorem ThreeSum.Scales.primeWindow_subpolynomial {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (primeWindow n : ℝ) ≤ (n : ℝ) ^ d := by sorry
