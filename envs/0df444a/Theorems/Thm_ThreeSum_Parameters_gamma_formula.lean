-- Prove2me | Theorems.Thm_ThreeSum_Parameters_gamma_formula
-- name    : ThreeSum.Parameters.gamma_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:56:08.297834+00:00
-- url     : https://prove2.me/theorems/8bf2e7df-4bf9-43c2-bf89-dadfbc4153ca
-- title:
--   Parameters: gamma formula
-- statement:
--   The Parameters construction uses the gamma formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L354-L368
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L354-L368

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_Parameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.Parameters
open Set Real
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048

theorem ThreeSum.Parameters.gamma_formula {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    gamma t = gammaNumerator t / Real.log 2 := by sorry
