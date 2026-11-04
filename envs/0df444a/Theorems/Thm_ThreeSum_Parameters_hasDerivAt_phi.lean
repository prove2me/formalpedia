-- Prove2me | Theorems.Thm_ThreeSum_Parameters_hasDerivAt_phi
-- name    : ThreeSum.Parameters.hasDerivAt_phi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:55:21.660455+00:00
-- url     : https://prove2.me/theorems/db3f2841-38d1-42d8-9232-3ec457b71558
-- title:
--   Parameters: has Deriv At phi
-- statement:
--   The Parameters construction uses the has Deriv At phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L370-L377
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Parameters.lean#L370-L377

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

theorem ThreeSum.Parameters.hasDerivAt_phi (t : ℝ) : HasDerivAt phi (phiDeriv t) t := by sorry
